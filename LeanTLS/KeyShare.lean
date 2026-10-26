/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Primitives.NIKE.NIKE
import Cryptlib.Primitives.NIKE.X25519
import Cryptlib.Primitives.KEM.KEM
import Cryptlib.Primitives.KEM.MLKEM.MLKEM768

namespace LeanTLS

open Cryptlib.Primitives.NIKE.NIKE (NIKE)
open Cryptlib.Primitives.KEM.KEM (KEM)

/-! # Key exchange groups

A TLS 1.3 named group (RFC 8446 §4.2.8) as a lawful structure: the client sends a share, the server
answers with its own share and a secret, and the client completes the same secret. The law `agree`
is that last sentence. Instances are built from Cryptlib's NIKEs and KEMs, whose own laws supply it,
and `concat` builds a hybrid group from two groups, with its `agree` assembled from theirs. -/

structure KeyShare where
  name  : String
  group : Nat

  ClientSecret : Type
  [secretI : Inhabited ClientSecret]

  entropySize     : Nat
  clientShareSize : Nat
  serverShareSize : Nat
  secretSize      : Nat

  clientGen : Vector UInt8 entropySize → ClientSecret × Vector UInt8 clientShareSize
  /-- `none` rejects the client's share. -/
  serverRespond : Vector UInt8 entropySize → Vector UInt8 clientShareSize →
    Option (Vector UInt8 serverShareSize × Vector UInt8 secretSize)
  /-- `none` rejects the server's share. -/
  clientFinish : ClientSecret → Vector UInt8 serverShareSize → Option (Vector UInt8 secretSize)

  /-- Client and server entropy under which the exchange cannot fail. `True` for a NIKE; a lattice
  KEM restricts it to draws that decapsulate correctly. -/
  Reliable : Vector UInt8 entropySize → Vector UInt8 entropySize → Prop

  /-- An honest client completes the secret the server derived from its share. -/
  agree : ∀ ec es, Reliable ec es → ∀ s k,
    serverRespond es (clientGen ec).2 = some (s, k) → clientFinish (clientGen ec).1 s = some k

attribute [instance] KeyShare.secretI

namespace KeyShare

/-! ## From a NIKE: the share is a public key, the secret the group action -/

section NIKEShare

variable (nike : NIKE)

def nikeGen (e : Vector UInt8 32) : nike.PrivateKey × Vector UInt8 nike.publicKeySize :=
  let sk := nike.privateKeyFromSeed e
  (sk, nike.encodePublicKey (nike.derivePublicKey sk))

def nikeFinish (sk : nike.PrivateKey) (share : Vector UInt8 nike.publicKeySize) :
    Option (Vector UInt8 nike.sharedSecretSize) :=
  match nike.decodePublicKey share with
  | some pk => if h : nike.Safe pk then some (nike.encodeSharedSecret (nike.groupAction sk ⟨pk, h⟩)) else none
  | none => none

def nikeRespond (e : Vector UInt8 32) (share : Vector UInt8 nike.publicKeySize) :
    Option (Vector UInt8 nike.publicKeySize × Vector UInt8 nike.sharedSecretSize) :=
  let (sk, mine) := nikeGen nike e
  (nikeFinish nike sk share).map (mine, ·)

theorem nikeFinish_derived (sk sk' : nike.PrivateKey) :
    nikeFinish nike sk (nike.encodePublicKey (nike.derivePublicKey sk')) =
      some (nike.encodeSharedSecret (nike.groupAction sk ⟨_, nike.derive_safe sk'⟩)) := by
  simp only [nikeFinish, nike.decode_encode_pub, dif_pos (nike.derive_safe sk')]

theorem nikeAgree (ec es : Vector UInt8 32) (s k) :
    nikeRespond nike es (nikeGen nike ec).2 = some (s, k) →
      nikeFinish nike (nikeGen nike ec).1 s = some k := by
  simp only [nikeRespond, nikeGen, nikeFinish_derived, Option.map_some, Option.some.injEq,
    Prod.mk.injEq]
  rintro ⟨rfl, rfl⟩
  rw [nikeFinish_derived, nike.commutes]

end NIKEShare

def ofNIKE (name : String) (group : Nat) (nike : NIKE) [Inhabited nike.PrivateKey] : KeyShare where
  name := name
  group := group
  ClientSecret := nike.PrivateKey
  entropySize := 32
  clientShareSize := nike.publicKeySize
  serverShareSize := nike.publicKeySize
  secretSize := nike.sharedSecretSize
  clientGen := nikeGen nike
  serverRespond := nikeRespond nike
  clientFinish := nikeFinish nike
  Reliable _ _ := True
  agree ec es _ := nikeAgree nike ec es

/-! ## From a KEM: the client's share is a public key, the server's a ciphertext -/

section KEMShare

variable (kem : KEM) (check : kem.PublicKey → Bool)

/-- Key generation from `e`; `default` when it fails, which `Reliable` rules out. -/
def kemGen (e : Vector UInt8 32) : kem.PrivateKey × Vector UInt8 kem.publicKeySize :=
  match kem.generate (kem.stateFromSeed e) with
  | .ok ⟨pk, sk, _⟩ _ => (sk, kem.encodePublicKey pk)
  | .error _ _ => (default, kem.encodePublicKey default)

def kemRespond (e : Vector UInt8 32) (share : Vector UInt8 kem.publicKeySize) :
    Option (Vector UInt8 kem.ciphertextSize × Vector UInt8 kem.plaintextSize) :=
  match kem.decodePublicKey share with
  | some pk =>
    if check pk then
      match kem.encap pk (kem.stateFromSeed e) with
      | .ok (c, k) _ => some (kem.encodeCiphertext c, kem.encodePlaintext k)
      | .error _ _ => none
    else none
  | none => none

def kemFinish (sk : kem.PrivateKey) (share : Vector UInt8 kem.ciphertextSize) :
    Option (Vector UInt8 kem.plaintextSize) :=
  match kem.decodeCiphertext share with
  | some c =>
    match kem.decap sk c default with
    | .ok k _ => some (kem.encodePlaintext k)
    | .error _ _ => none
  | none => none

/-- Key generation succeeds and the server's draw decapsulates correctly. -/
def KemReliable (ec es : Vector UInt8 32) : Prop :=
  (∃ r t, kem.generate (kem.stateFromSeed ec) = .ok r t) ∧ kem.Reliable (kem.stateFromSeed es)

theorem kemAgree (ec es : Vector UInt8 32) (hr : KemReliable kem ec es) (s k) :
    kemRespond kem check es (kemGen kem ec).2 = some (s, k) →
      kemFinish kem (kemGen kem ec).1 s = some k := by
  obtain ⟨⟨⟨pk, sk, hkp⟩, t, hgen⟩, hrel⟩ := hr
  simp only [kemGen, hgen, kemRespond, kemFinish, kem.decode_encode_pub]
  intro h
  split at h
  · split at h
    · rename_i c k' t' henc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨t'', hdec⟩ := hkp _ hrel c k' t' henc default
      simp only [kem.decode_encode_ct, hdec]
    · exact absurd h (by simp)
  · exact absurd h (by simp)

end KEMShare

def ofKEM (name : String) (group : Nat) (kem : KEM) (check : kem.PublicKey → Bool) : KeyShare where
  name := name
  group := group
  ClientSecret := kem.PrivateKey
  entropySize := 32
  clientShareSize := kem.publicKeySize
  serverShareSize := kem.ciphertextSize
  secretSize := kem.plaintextSize
  clientGen := kemGen kem
  serverRespond := kemRespond kem check
  clientFinish := kemFinish kem
  Reliable := KemReliable kem
  agree := kemAgree kem check

/-! ## Concatenation: two groups side by side

Shares, secrets and entropy are concatenated, the first group's first. This is the shape of the
hybrid groups of draft-ietf-tls-ecdhe-mlkem. -/

section Concat

variable {m n : Nat}

def left (v : Vector UInt8 (m + n)) : Vector UInt8 m :=
  Vector.ofFn fun i : Fin m => v[i.val]'(by omega)

def right (v : Vector UInt8 (m + n)) : Vector UInt8 n :=
  Vector.ofFn fun i : Fin n => v[m + i.val]'(by omega)

@[simp] theorem left_append (a : Vector UInt8 m) (b : Vector UInt8 n) : left (a ++ b) = a := by
  ext i hi
  simp [left]

@[simp] theorem right_append (a : Vector UInt8 m) (b : Vector UInt8 n) : right (a ++ b) = b := by
  ext i hi
  simp [right]

end Concat

def concat (name : String) (group : Nat) (A B : KeyShare) : KeyShare where
  name := name
  group := group
  ClientSecret := A.ClientSecret × B.ClientSecret
  entropySize := A.entropySize + B.entropySize
  clientShareSize := A.clientShareSize + B.clientShareSize
  serverShareSize := A.serverShareSize + B.serverShareSize
  secretSize := A.secretSize + B.secretSize
  clientGen e :=
    let (sa, ca) := A.clientGen (left e)
    let (sb, cb) := B.clientGen (right e)
    ((sa, sb), ca ++ cb)
  serverRespond e share := do
    let (sa, ka) ← A.serverRespond (left e) (left share)
    let (sb, kb) ← B.serverRespond (right e) (right share)
    some (sa ++ sb, ka ++ kb)
  clientFinish sk share := do
    let ka ← A.clientFinish sk.1 (left share)
    let kb ← B.clientFinish sk.2 (right share)
    some (ka ++ kb)
  Reliable ec es := A.Reliable (left ec) (left es) ∧ B.Reliable (right ec) (right es)
  agree ec es hr s k h := by
    simp only [left_append, right_append, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at h ⊢
    obtain ⟨⟨sa, ka⟩, ha, ⟨sb, kb⟩, hb, hs⟩ := h
    simp only [Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    refine ⟨ka, ?_, kb, ?_, rfl⟩
    · simpa using A.agree _ _ hr.1 sa ka ha
    · simpa using B.agree _ _ hr.2 sb kb hb

end KeyShare

/-! ## The groups lean_tls offers -/

open Cryptlib.Primitives.KEM.FIPS203 (checkEncapsulationKey)

instance : Inhabited Cryptlib.Primitives.NIKE.X25519.Scheme.PrivateKey :=
  ⟨Cryptlib.Primitives.NIKE.X25519.Scheme.privateKeyFromSeed (Vector.replicate 32 0)⟩

/-- `x25519` (0x001d), over Cryptlib's group formulation of X25519, whose commutativity is
proved. -/
def x25519 : KeyShare := KeyShare.ofNIKE "x25519" 0x001d Cryptlib.Primitives.NIKE.X25519.Scheme

/-- ML-KEM-768 with the FIPS 203 §7.2 encapsulation key check. -/
def mlkem768 : KeyShare :=
  KeyShare.ofKEM "MLKEM768" 0x0201 Cryptlib.Primitives.KEM.MLKEM768.kemMLKEM768
    fun pk => checkEncapsulationKey .MLKEM768 pk.1

/-- `X25519MLKEM768` (0x11ec, draft-ietf-tls-ecdhe-mlkem): the ML-KEM-768 share first, then
X25519's; the secret is `mlkem_ss ‖ x25519_ss`. -/
def x25519mlkem768 : KeyShare := KeyShare.concat "X25519MLKEM768" 0x11ec mlkem768 x25519

/-- The groups by name, for configurations that must stay in `Type`. -/
inductive Group where
  | x25519mlkem768
  | x25519
  | mlkem768
deriving DecidableEq, Repr, Inhabited

def Group.keyShare : Group → KeyShare
  | .x25519mlkem768 => LeanTLS.x25519mlkem768
  | .x25519 => LeanTLS.x25519
  | .mlkem768 => LeanTLS.mlkem768

end LeanTLS

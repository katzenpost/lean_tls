/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import LeanTLS.Alert
import LeanTLS.CipherSuite
import LeanTLS.KeySchedule
import LeanTLS.KeyShare
import LeanTLS.Messages
import Cryptlib.Primitives.Sign.Ed25519_verify
import Cryptlib.Primitives.Sign.MLDSA.MLDSA
import Cryptlib.Util.ConstantTime

namespace LeanTLS.Handshake

open LeanTLS.Messages
open Cryptlib.Primitives.KDF.HKDF (expand)
open Cryptlib.Util.Bytes (toVecN ofVector)

/-! # What the client and server handshakes share

A handshake is a pure state machine over the CRYPTO streams of QUIC's three encryption levels
(RFC 9001 §4). It is given the bytes that arrived at a level, in order, and answers with bytes to
send at a level and the traffic secrets to install. It performs no IO and draws no randomness:
each connection is given a 32-byte entropy seed, expanded per use. -/

inductive Level where
  | initial
  | handshake
  | application
deriving DecidableEq, Repr, Inhabited

/-- Read and write secrets for one level. Deliberately without `Repr`: secrets are not printed. -/
structure Secrets where
  read  : ByteArray
  write : ByteArray
deriving Inhabited

inductive Output where
  | send (level : Level) (data : ByteArray)
  | install (level : Level) (suite : Suite) (secrets : Secrets)

/-- `n` bytes for the named use, from the connection's seed. -/
def draw (seed : Vector UInt8 32) (label : String) (n : Nat) : ByteArray :=
  expand KeySchedule.H (ofVector seed) ("lean_tls " ++ label).toUTF8 n

def drawVec (seed : Vector UInt8 32) (label : String) (n : Nat) : Vector UInt8 n :=
  toVecN n (draw seed label n)

instance : LawfulBEq ByteArray where
  eq_of_beq {a b} h := ByteArray.ext (eq_of_beq (show (a.data == b.data) = true from h))
  rfl {a} := (beq_self_eq_true a.data : (a.data == a.data) = true)

/-- Byte equality that inspects every byte, whatever the first difference: Cryptlib's, with
`ctEq_iff` to say it is equality. -/
abbrev ctEq := Cryptlib.Util.ConstantTime.ctEq

/-- The input a CertificateVerify signs (RFC 8446 §4.4.3). -/
def certVerifyInput (server : Bool) (transcript : ByteArray) : ByteArray :=
  ⟨Array.replicate 64 0x20⟩ ++
    (if server then "TLS 1.3, server CertificateVerify" else "TLS 1.3, client CertificateVerify").toUTF8 ++
    ⟨#[0]⟩ ++ KeySchedule.hash transcript

abbrev ed25519 := Cryptlib.Primitives.Sign.Ed25519Verify.nativeSignature
abbrev mldsa65Sig := Cryptlib.Primitives.Sign.FIPS204.mldsa65Signature
abbrev ed25519Sig := ed25519

def schemeEd25519 : Nat := 0x0807
/-- ML-DSA-65's SignatureScheme (draft-ietf-tls-mldsa). -/
def schemeMLDSA65 : Nat := 0x0905

/-- How a server authenticates: Ed25519, or ML-DSA-65 for post-quantum authentication. Either
way its private key is a 32-byte seed. -/
inductive Scheme where
  | ed25519
  | mldsa65
deriving DecidableEq, Repr, Inhabited

def Scheme.code : Scheme → Nat
  | .ed25519 => schemeEd25519
  | .mldsa65 => schemeMLDSA65

/-- A server's public key, as its certificate carries it. -/
inductive AuthKey where
  | ed25519 (key : Vector UInt8 32)
  /-- The FIPS 204 encoding, 1952 bytes. -/
  | mldsa65 (key : ByteArray)

def AuthKey.scheme : AuthKey → Scheme
  | .ed25519 _ => .ed25519
  | .mldsa65 _ => .mldsa65

/-- Whether `sig` is the key's signature on `input`. -/
def AuthKey.verify : AuthKey → ByteArray → ByteArray → Bool
  | .ed25519 key, input, sig => sig.size == 64 && ed25519Sig.verify key input (toVecN 64 sig)
  | .mldsa65 key, input, sig => key.size == mldsa65Sig.publicKeySize &&
      sig.size == mldsa65Sig.sigSize &&
        mldsa65Sig.verify (toVecN mldsa65Sig.publicKeySize key) input (toVecN mldsa65Sig.sigSize sig)

/-- The public key for a private key seed. -/
def Scheme.authKey : Scheme → Vector UInt8 32 → AuthKey
  | .ed25519, sk => .ed25519 (ed25519Sig.pub sk)
  | .mldsa65, sk => .mldsa65 (ofVector (n := mldsa65Sig.publicKeySize) (mldsa65Sig.pub sk))

/-- ML-DSA's signing state: its randomness, from the connection's seed. -/
@[irreducible] def mldsaState (seed : Vector UInt8 32) : Cryptlib.Primitives.Sign.FIPS204.State :=
  (0, drawVec seed "mldsa65 rnd" 32)

/-- A signer's result, as the handshake sees it: an abort is an internal error. -/
def signResult {σ α : Type} : EStateM.Result Cryptlib.Primitives.Sign.Sign.SignError σ α → Except Alert α
  | .ok a _ => .ok a
  | .error _ _ => .error .internalError

/-- The signature on a CertificateVerify input; ML-DSA's randomness comes from the connection's
seed, and its signer may give up, a negligible chance. -/
def Scheme.sign : Scheme → Vector UInt8 32 → Vector UInt8 32 → ByteArray → Except Alert ByteArray
  | .ed25519, sk, _, input => pure (ofVector (Cryptlib.Primitives.Sign.Ed25519Math.signNative sk input))
  | .mldsa65, sk, seed, input =>
    (signResult (mldsa65Sig.sign sk input (mldsaState seed))).map (ofVector (n := mldsa65Sig.sigSize))

theorem verify_ed25519 (pk : Vector UInt8 32) (input : ByteArray) (σ : Vector UInt8 64)
    (h : ed25519Sig.verify pk input σ = true) : (AuthKey.ed25519 pk).verify input (ofVector σ) = true := by
  have hs : (ofVector σ).size = 64 := Cryptlib.Util.Bytes.size_ofVector σ
  simp only [AuthKey.verify]
  rw [hs, Cryptlib.Util.Bytes.toVecN_ofVector, h]
  rfl

theorem verify_mldsa65 (pk : mldsa65Sig.PublicKey) (input : ByteArray) (σ : mldsa65Sig.Sig)
    (h : mldsa65Sig.verify pk input σ = true) :
    (AuthKey.mldsa65 (ofVector (n := mldsa65Sig.publicKeySize) pk)).verify input
      (ofVector (n := mldsa65Sig.sigSize) σ) = true := by
  have hp : (ofVector (n := mldsa65Sig.publicKeySize) pk).size = mldsa65Sig.publicKeySize :=
    Cryptlib.Util.Bytes.size_ofVector _
  have hs : (ofVector (n := mldsa65Sig.sigSize) σ).size = mldsa65Sig.sigSize :=
    Cryptlib.Util.Bytes.size_ofVector _
  simp only [AuthKey.verify]
  rw [hp, hs, Cryptlib.Util.Bytes.toVecN_ofVector (n := mldsa65Sig.publicKeySize) pk,
    Cryptlib.Util.Bytes.toVecN_ofVector (n := mldsa65Sig.sigSize) σ, h]
  simp

theorem sign_ed25519_eq (sk seed : Vector UInt8 32) (input : ByteArray) :
    Scheme.ed25519.sign sk seed input =
      .ok (ofVector (Cryptlib.Primitives.Sign.Ed25519Math.signNative sk input)) := rfl

/-- What a scheme signs verifies under its public key. -/
theorem Scheme.verify_sign (sch : Scheme) (sk seed : Vector UInt8 32) (input sig : ByteArray)
    (h : sch.sign sk seed input = .ok sig) : (sch.authKey sk).verify input sig = true := by
  cases sch with
  | ed25519 =>
    have hsig := Except.ok.inj ((sign_ed25519_eq sk seed input).symm.trans h)
    rw [← hsig]
    exact verify_ed25519 _ input _ (ed25519Sig.verify_sign sk input () _ ()
      (Cryptlib.Primitives.Sign.Ed25519Verify.nativeSignature_sign sk input ()))
  | mldsa65 =>
    have e : Scheme.mldsa65.sign sk seed input =
        (signResult (mldsa65Sig.sign sk input (mldsaState seed))).map
          (ofVector (n := mldsa65Sig.sigSize)) := rfl
    rw [e] at h
    rcases hs : mldsa65Sig.sign sk input (mldsaState seed) with ⟨σ, s'⟩ | ⟨err, s'⟩
    · rw [hs] at h
      rw [← Except.ok.inj h]
      exact verify_mldsa65 _ input σ (mldsa65Sig.verify_sign sk input _ σ s' hs)
    · rw [hs] at h
      nomatch h

theorem mldsa65_sigSize : mldsa65Sig.sigSize = 3309 := by decide

/-- A signature takes at most 3309 bytes. -/
theorem Scheme.sign_size (sch : Scheme) (sk seed : Vector UInt8 32) (input sig : ByteArray)
    (h : sch.sign sk seed input = .ok sig) : sig.size ≤ 3309 := by
  cases sch with
  | ed25519 =>
    rw [← Except.ok.inj ((sign_ed25519_eq sk seed input).symm.trans h)]
    simp
  | mldsa65 =>
    have e : Scheme.mldsa65.sign sk seed input =
        (signResult (mldsa65Sig.sign sk input (mldsaState seed))).map
          (ofVector (n := mldsa65Sig.sigSize)) := rfl
    rw [e] at h
    rcases hs : mldsa65Sig.sign sk input (mldsaState seed) with ⟨σ, s'⟩ | ⟨err, s'⟩
    · rw [hs] at h
      rw [← Except.ok.inj h, Cryptlib.Util.Bytes.size_ofVector (n := mldsa65Sig.sigSize) σ,
        mldsa65_sigSize]
    · rw [hs] at h
      nomatch h

theorem Scheme.authKey_scheme (sch : Scheme) (sk : Vector UInt8 32) : (sch.authKey sk).scheme = sch := by
  cases sch <;> rfl

/-- Ed25519 always signs. -/
theorem Scheme.sign_ed25519 (sk seed : Vector UInt8 32) (input : ByteArray) :
    ∃ sig, Scheme.ed25519.sign sk seed input = .ok sig := ⟨_, sign_ed25519_eq sk seed input⟩

/-- Bytes waiting at each level for the rest of a message. -/
structure Buffers where
  initial     : ByteArray := ByteArray.empty
  handshake   : ByteArray := ByteArray.empty
  application : ByteArray := ByteArray.empty

namespace Buffers

def get (b : Buffers) : Level → ByteArray
  | .initial => b.initial
  | .handshake => b.handshake
  | .application => b.application

def set (b : Buffers) : Level → ByteArray → Buffers
  | .initial, x => { b with initial := x }
  | .handshake, x => { b with handshake := x }
  | .application, x => { b with application := x }

end Buffers

def ext (typ : Nat) (body : Wire.Writer Unit) : Except Alert Extension := do
  pure { typ, data := ← Wire.Writer.run body }

def require {α : Type} (o : Option α) (a : Alert) : Except Alert α :=
  match o with
  | some x => pure x
  | none => throw a

end LeanTLS.Handshake

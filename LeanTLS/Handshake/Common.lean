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

/-- The input an Ed25519 CertificateVerify signs (RFC 8446 §4.4.3). -/
def certVerifyInput (server : Bool) (transcript : ByteArray) : ByteArray :=
  ⟨Array.replicate 64 0x20⟩ ++
    (if server then "TLS 1.3, server CertificateVerify" else "TLS 1.3, client CertificateVerify").toUTF8 ++
    ⟨#[0]⟩ ++ KeySchedule.hash transcript

abbrev ed25519 := Cryptlib.Primitives.Sign.Ed25519Verify.nativeSignature

def schemeEd25519 : Nat := 0x0807

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

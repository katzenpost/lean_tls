/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Primitives.KDF.HKDF
import Cryptlib.Primitives.MAC.HMAC
import Cryptlib.Primitives.Hash.Sha2
import Cryptlib.Util.Bytes

namespace LeanTLS.KeySchedule

open Cryptlib.Primitives.KDF.HKDF (extract expand expand_size)
open Cryptlib.Primitives.MAC.HMAC (hmacSha256)
open Cryptlib.Util.Bytes (ofVector)

/-! # The TLS 1.3 key schedule over SHA-256 (RFC 8446 §7.1)

Both cipher suites lean_tls negotiates use SHA-256. Secrets are 32 bytes. -/

abbrev H := Cryptlib.Primitives.Hash.Sha2.Sha256.Scheme

def hash (m : ByteArray) : ByteArray := ofVector (H.hash m)

def zeros : ByteArray := ⟨Array.replicate 32 0⟩

def hkdfExtract (salt ikm : ByteArray) : ByteArray := ofVector (extract H salt ikm)

/-- `HkdfLabel`: `u16 length ‖ opaque8 ("tls13 " ‖ label) ‖ opaque8 context`. -/
def hkdfLabel (len : Nat) (label context : ByteArray) : ByteArray :=
  let full := "tls13 ".toUTF8 ++ label
  ⟨#[UInt8.ofNat (len >>> 8), UInt8.ofNat len, UInt8.ofNat full.size]⟩ ++ full ++
    ⟨#[UInt8.ofNat context.size]⟩ ++ context

def expandLabel (secret : ByteArray) (label : String) (context : ByteArray) (len : Nat) : ByteArray :=
  expand H secret (hkdfLabel len label.toUTF8 context) len

theorem expandLabel_size (secret : ByteArray) (label : String) (context : ByteArray) (len : Nat) :
    (expandLabel secret label context len).size = len :=
  expand_size H secret _ len

def deriveSecret (secret : ByteArray) (label : String) (transcript : ByteArray) : ByteArray :=
  expandLabel secret label (hash transcript) 32

/-- `HMAC(finished_key, Transcript-Hash)` (RFC 8446 §4.4.4). -/
def finishedData (baseKey transcript : ByteArray) : ByteArray :=
  ofVector (hmacSha256 (expandLabel baseKey "finished" ByteArray.empty 32) (hash transcript))

def earlySecret : ByteArray := hkdfExtract ByteArray.empty zeros

def handshakeSecret (sharedSecret : ByteArray) : ByteArray :=
  hkdfExtract (deriveSecret earlySecret "derived" ByteArray.empty) sharedSecret

def masterSecret (hs : ByteArray) : ByteArray :=
  hkdfExtract (deriveSecret hs "derived" ByteArray.empty) zeros

/-- Client and server secrets for one direction pair. -/
structure TrafficSecrets where
  client : ByteArray
  server : ByteArray

/-- Handshake traffic secrets, from the transcript through ServerHello. -/
def handshakeTraffic (hs transcript : ByteArray) : TrafficSecrets :=
  { client := deriveSecret hs "c hs traffic" transcript,
    server := deriveSecret hs "s hs traffic" transcript }

/-- Application traffic secrets, from the transcript through the server's Finished. -/
def applicationTraffic (ms transcript : ByteArray) : TrafficSecrets :=
  { client := deriveSecret ms "c ap traffic" transcript,
    server := deriveSecret ms "s ap traffic" transcript }

/-! ## QUIC packet protection keys (RFC 9001 §5.1) -/

structure PacketKeys where
  key : ByteArray
  iv  : ByteArray
  hp  : ByteArray

def quicKeys (secret : ByteArray) (keyLen : Nat) : PacketKeys :=
  { key := expandLabel secret "quic key" ByteArray.empty keyLen,
    iv  := expandLabel secret "quic iv" ByteArray.empty 12,
    hp  := expandLabel secret "quic hp" ByteArray.empty keyLen }

/-- The next generation of a 1-RTT secret, for a key update (RFC 9001 §6.1). -/
def quicNextSecret (secret : ByteArray) : ByteArray :=
  expandLabel secret "quic ku" ByteArray.empty 32

end LeanTLS.KeySchedule

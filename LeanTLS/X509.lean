/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import LeanTLS.Alert
import LeanTLS.Handshake.Common

namespace LeanTLS.X509

open Cryptlib.Util.Bytes (toVecN)

/-! # The X.509 lean_tls needs

Peers are authenticated by pinning `SHA-256(SubjectPublicKeyInfo)`, as katzenpost's QUIC transport
does, so a certificate is read only for its SPKI and its Ed25519 or ML-DSA-65 key. Chains, names, validity and
extensions are not interpreted. Certificates are produced in the shape katzenpost's
`epochCertificate` produces: self-signed Ed25519, empty names, no extensions.

DER is read strictly: definite minimal lengths, single-byte tags, nothing after the outer value. -/

structure TLV where
  tag     : UInt8
  /-- The whole encoding, header included. -/
  raw     : ByteArray
  content : ByteArray
deriving Inhabited

/-- The value at `pos`, and the position after it. -/
def readTLV (b : ByteArray) (pos : Nat) : Except Alert (TLV × Nat) := do
  if pos + 2 > b.size then throw .badCertificate
  let tag := b.get! pos
  if tag &&& 0x1f == 0x1f then throw .badCertificate
  let l0 := (b.get! (pos + 1)).toNat
  let (len, hdr) ←
    if l0 < 0x80 then pure (l0, 2)
    else if l0 == 0x81 then
      if pos + 3 > b.size then throw .badCertificate
      let l := (b.get! (pos + 2)).toNat
      if l < 0x80 then throw .badCertificate
      pure (l, 3)
    else if l0 == 0x82 then
      if pos + 4 > b.size then throw .badCertificate
      let l := (b.get! (pos + 2)).toNat * 256 + (b.get! (pos + 3)).toNat
      if l < 0x100 then throw .badCertificate
      pure (l, 4)
    else throw .badCertificate
  if pos + hdr + len > b.size then throw .badCertificate
  pure ({ tag, raw := b.extract pos (pos + hdr + len),
          content := b.extract (pos + hdr) (pos + hdr + len) }, pos + hdr + len)

/-- The children of a constructed value, in order. -/
def children (b : ByteArray) : Except Alert (Array TLV) := do
  let mut pos := 0
  let mut out := #[]
  for _ in [0:b.size] do
    if pos ≥ b.size then break
    let (t, next) ← readTLV b pos
    out := out.push t
    pos := next
  pure out

def tagSequence : UInt8 := 0x30
def tagBitString : UInt8 := 0x03
def tagOID : UInt8 := 0x06

/-- `id-Ed25519`, 1.3.101.112 (RFC 8410). -/
def oidEd25519 : ByteArray := ⟨#[0x2b, 0x65, 0x70]⟩

/-- `id-ml-dsa-65`, 2.16.840.1.101.3.4.3.18 (RFC 9881). -/
def oidMLDSA65 : ByteArray := ⟨#[0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x03, 0x12]⟩

structure Leaf where
  /-- The SubjectPublicKeyInfo as encoded, the input to the pin. -/
  spki : ByteArray
  /-- The key, when it is Ed25519 or ML-DSA-65. -/
  key : Option Handshake.AuthKey

/-- The SPKI of a certificate, and its key when that key is Ed25519 or ML-DSA-65. -/
def parseLeaf (der : ByteArray) : Except Alert Leaf := do
  let (cert, endPos) ← readTLV der 0
  if cert.tag != tagSequence || endPos != der.size then throw .badCertificate
  let parts ← children cert.content
  let some tbs := parts[0]? | throw .badCertificate
  if tbs.tag != tagSequence then throw .badCertificate
  let fields ← children tbs.content
  -- version [0] is optional; then serial, signature, issuer, validity, subject, SPKI.
  let base := if fields[0]?.map (·.tag) == some 0xa0 then 1 else 0
  let some spki := fields[base + 5]? | throw .badCertificate
  if spki.tag != tagSequence then throw .badCertificate
  let sp ← children spki.content
  let (some alg, some key) := (sp[0]?, sp[1]?) | throw .badCertificate
  if alg.tag != tagSequence || key.tag != tagBitString || sp.size != 2 then throw .badCertificate
  let algParts ← children alg.content
  let oid := if algParts.size == 1 && algParts[0]!.tag == tagOID then algParts[0]!.content
    else ByteArray.empty
  let bits := key.content
  let k : Option Handshake.AuthKey :=
    if bits.size == 0 || bits.get! 0 != 0 then none
    else if oid == oidEd25519 && bits.size == 33 then some (.ed25519 (toVecN 32 (bits.extract 1 33)))
    else if oid == oidMLDSA65 && bits.size == 1953 then some (.mldsa65 (bits.extract 1 1953))
    else none
  pure { spki := spki.raw, key := k }

/-! ## Encoding -/

def encodeLength (n : Nat) : ByteArray :=
  if n < 0x80 then ⟨#[UInt8.ofNat n]⟩
  else if n < 0x100 then ⟨#[0x81, UInt8.ofNat n]⟩
  else ⟨#[0x82, UInt8.ofNat (n >>> 8), UInt8.ofNat n]⟩

def tlv (tag : UInt8) (content : ByteArray) : ByteArray :=
  ⟨#[tag]⟩ ++ encodeLength content.size ++ content

def sequence (parts : List ByteArray) : ByteArray :=
  tlv tagSequence (parts.foldl (· ++ ·) ByteArray.empty)

def ed25519AlgId : ByteArray := sequence [tlv tagOID oidEd25519]

def ed25519Spki (key : ByteArray) : ByteArray :=
  sequence [ed25519AlgId, tlv tagBitString (⟨#[0]⟩ ++ key)]

def mldsa65AlgId : ByteArray := sequence [tlv tagOID oidMLDSA65]

def mldsa65Spki (key : ByteArray) : ByteArray :=
  sequence [mldsa65AlgId, tlv tagBitString (⟨#[0]⟩ ++ key)]

/-- `YYMMDDHHMMSSZ` for a Unix time in 1950–2049 (RFC 5280 §4.1.2.5.1). -/
def utcTime (unix : Nat) : ByteArray :=
  let days := unix / 86400
  let secs := unix % 86400
  -- Civil date from days since 1970-01-01 (H. Hinnant's algorithm).
  let z := days + 719468
  let era := z / 146097
  let doe := z - era * 146097
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp := (5 * doy + 2) / 153
  let d := doy - (153 * mp + 2) / 5 + 1
  let m := if mp < 10 then mp + 3 else mp - 9
  let y := yoe + era * 400 + (if m ≤ 2 then 1 else 0)
  let two (n : Nat) : String := if n < 10 then s!"0{n}" else toString n
  let s := two (y % 100) ++ two m ++ two d ++ two (secs / 3600) ++ two (secs / 60 % 60) ++
    two (secs % 60) ++ "Z"
  tlv 0x17 s.toUTF8

/-- A self-signed certificate in the shape of katzenpost's `epochCertificate`, for the signature
algorithm `algId` and the key `spki`. `serial` is 16 bytes; its top bit is set and it is encoded
positive. -/
def selfSignedWith {ε : Type} (algId spki : ByteArray)
    (sign : ByteArray → Except ε ByteArray) (serial : ByteArray) (notBefore notAfter : Nat) :
    Except ε ByteArray := do
  let serialBytes := serial.set! 0 (serial.get! 0 ||| 0x80)
  let tbs := sequence [
    tlv 0xa0 (tlv 0x02 ⟨#[2]⟩),
    tlv 0x02 (⟨#[0]⟩ ++ serialBytes),
    algId,
    sequence [],
    sequence [utcTime notBefore, utcTime notAfter],
    sequence [],
    spki]
  pure (sequence [tbs, algId, tlv tagBitString (⟨#[0]⟩ ++ (← sign tbs))])

/-- A self-signed Ed25519 certificate in the shape of katzenpost's `epochCertificate`. -/
def selfSigned (sign : ByteArray → ByteArray) (key serial : ByteArray)
    (notBefore notAfter : Nat) : ByteArray :=
  match selfSignedWith (ε := Empty) ed25519AlgId (ed25519Spki key) (fun tbs => .ok (sign tbs)) serial
      notBefore notAfter with
  | .ok c => c
  | .error e => nomatch e

/-- A self-signed certificate for a server's scheme and private key seed. -/
def certificateFor (sch : Handshake.Scheme) (sk seed serial : ByteArray) (notBefore notAfter : Nat) :
    Except Alert ByteArray :=
  let sk := toVecN 32 sk
  match sch.authKey sk with
  | .ed25519 key => pure (selfSigned (fun tbs => Cryptlib.Util.Bytes.ofVector
      (Cryptlib.Primitives.Sign.Ed25519Math.signNative sk tbs)) (Cryptlib.Util.Bytes.ofVector key)
      serial notBefore notAfter)
  | .mldsa65 key => selfSignedWith mldsa65AlgId (mldsa65Spki key)
      (sch.sign sk (toVecN 32 seed)) serial notBefore notAfter

end LeanTLS.X509

/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import LeanTLS.Alert

namespace LeanTLS.X509

/-! # The X.509 lean_tls needs

Peers are authenticated by pinning `SHA-256(SubjectPublicKeyInfo)`, as katzenpost's QUIC transport
does, so a certificate is read only for its SPKI and Ed25519 key. Chains, names, validity and
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

structure Leaf where
  /-- The SubjectPublicKeyInfo as encoded, the input to the pin. -/
  spki : ByteArray
  ed25519Key : Option ByteArray

/-- The SPKI of a certificate, and its key when that key is Ed25519. -/
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
  let isEd := algParts.size == 1 && algParts[0]!.tag == tagOID && algParts[0]!.content == oidEd25519
  let ed := if isEd && key.content.size == 33 && key.content.get! 0 == 0 then
      some (key.content.extract 1 33) else none
  pure { spki := spki.raw, ed25519Key := ed }

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

/-- A self-signed Ed25519 certificate in the shape of katzenpost's `epochCertificate`. `serial` is
16 bytes; its top bit is set and it is encoded positive. -/
def selfSigned (sign : ByteArray → ByteArray) (key serial : ByteArray)
    (notBefore notAfter : Nat) : ByteArray :=
  let serialBytes := serial.set! 0 (serial.get! 0 ||| 0x80)
  let tbs := sequence [
    tlv 0xa0 (tlv 0x02 ⟨#[2]⟩),
    tlv 0x02 (⟨#[0]⟩ ++ serialBytes),
    ed25519AlgId,
    sequence [],
    sequence [utcTime notBefore, utcTime notAfter],
    sequence [],
    ed25519Spki key]
  sequence [tbs, ed25519AlgId, tlv tagBitString (⟨#[0]⟩ ++ sign tbs)]

end LeanTLS.X509

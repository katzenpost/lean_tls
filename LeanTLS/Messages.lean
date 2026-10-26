/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import LeanTLS.Wire

namespace LeanTLS.Messages

open LeanTLS.Wire

/-! # Handshake messages

The TLS 1.3 handshake messages a QUIC connection exchanges (RFC 8446 §4), decoded at one
boundary into typed records. Extensions stay as raw bodies, decoded on demand by the functions
below. A message list never holds two extensions of one type. -/

namespace HandshakeType
def clientHello         : UInt8 := 1
def serverHello         : UInt8 := 2
def newSessionTicket    : UInt8 := 4
def encryptedExtensions : UInt8 := 8
def certificate         : UInt8 := 11
def certificateRequest  : UInt8 := 13
def certificateVerify   : UInt8 := 15
def finished            : UInt8 := 20
def keyUpdate           : UInt8 := 24
end HandshakeType

namespace ExtType
def serverName              : Nat := 0
def supportedGroups         : Nat := 10
def signatureAlgorithms     : Nat := 13
def alpn                    : Nat := 16
def supportedVersions       : Nat := 43
def pskKeyExchangeModes     : Nat := 45
def keyShare                : Nat := 51
def quicTransportParameters : Nat := 57
end ExtType

def tls13 : Nat := 0x0304
def legacyVersion : Nat := 0x0303

/-- `SHA-256("HelloRetryRequest")`, the random of a HelloRetryRequest (RFC 8446 §4.1.3). -/
def helloRetryRandom : ByteArray := ⟨#[
  0xcf, 0x21, 0xad, 0x74, 0xe5, 0x9a, 0x61, 0x11, 0xbe, 0x1d, 0x8c, 0x02, 0x1e, 0x65, 0xb8, 0x91,
  0xc2, 0xa2, 0x11, 0x16, 0x7a, 0xbb, 0x8c, 0x5e, 0x07, 0x9e, 0x09, 0xe2, 0xc8, 0xa8, 0x33, 0x9c]⟩

structure Extension where
  typ  : Nat
  data : ByteArray

def extension : Parser Extension := do
  let typ ← Parser.u16
  let data ← Parser.opaque16
  pure { typ, data }

def writeExtension (e : Extension) : Writer Unit := do
  Writer.u16 e.typ
  Writer.opaque16 e.data

/-- Whether two extensions in a list have the same type. -/
def dupTypes : List Extension → Bool
  | [] => false
  | e :: es => es.any (·.typ == e.typ) || dupTypes es

/-- Extensions, at most one of each type. -/
def extensions : Parser (Array Extension) := do
  let exts ← Parser.vec16 (Parser.many extension)
  if dupTypes exts.toList then throw .illegalParameter
  pure exts

def writeExtensions (exts : Array Extension) : Writer Unit :=
  Writer.prefixed 2 do
    for e in exts do
      writeExtension e

def find (exts : Array Extension) (typ : Nat) : Option ByteArray :=
  (exts.find? (·.typ == typ)).map (·.data)

/-- Decode one extension body completely; a malformed body is `decodeError`. -/
def decodeExt {α : Type} (p : Parser α) (b : ByteArray) : Except Alert α := Parser.run p b

def u16List : Parser (Array Nat) := Parser.many Parser.u16

structure KeyShareEntry where
  group : Nat
  key   : ByteArray

def keyShareEntry : Parser KeyShareEntry := do
  let group ← Parser.u16
  let key ← Parser.opaque16
  pure { group, key }

def writeKeyShareEntry (e : KeyShareEntry) : Writer Unit := do
  Writer.u16 e.group
  Writer.opaque16 e.key

/-- ALPN protocol names (RFC 7301 §3.1), each non-empty. -/
def alpnList : Parser (Array ByteArray) := Parser.vec16 (Parser.many do
  let p ← Parser.opaque8
  if p.size == 0 then Parser.fail else pure p)

def writeAlpnList (ps : Array ByteArray) : Writer Unit :=
  Writer.prefixed 2 (for p in ps do Writer.opaque8 p)

structure ClientHello where
  random       : ByteArray
  sessionId    : ByteArray
  cipherSuites : Array Nat
  extensions   : Array Extension

structure ServerHello where
  random       : ByteArray
  sessionId    : ByteArray
  cipherSuite  : Nat
  extensions   : Array Extension

structure CertificateEntry where
  data       : ByteArray
  extensions : ByteArray

structure Certificate where
  context : ByteArray
  entries : Array CertificateEntry

structure CertificateVerify where
  scheme    : Nat
  signature : ByteArray

def clientHello : Parser ClientHello := do
  if (← Parser.u16) != legacyVersion then throw .protocolVersion
  let random ← Parser.bytes 32
  let sessionId ← Parser.opaque8
  if sessionId.size > 32 then Parser.fail
  let cipherSuites ← Parser.vec16 u16List
  let compression ← Parser.opaque8
  if compression.data != #[0] then throw .illegalParameter
  let extensions ← extensions
  pure { random, sessionId, cipherSuites, extensions }

def writeClientHello (m : ClientHello) : Writer Unit := do
  Writer.u16 legacyVersion
  Writer.bytes m.random
  Writer.opaque8 m.sessionId
  Writer.prefixed 2 (for s in m.cipherSuites do Writer.u16 s)
  Writer.opaque8 ⟨#[0]⟩
  writeExtensions m.extensions

def serverHello : Parser ServerHello := do
  if (← Parser.u16) != legacyVersion then throw .protocolVersion
  let random ← Parser.bytes 32
  let sessionId ← Parser.opaque8
  if sessionId.size > 32 then Parser.fail
  let cipherSuite ← Parser.u16
  if (← Parser.u8) != 0 then throw .illegalParameter
  let extensions ← extensions
  pure { random, sessionId, cipherSuite, extensions }

def writeServerHello (m : ServerHello) : Writer Unit := do
  Writer.u16 legacyVersion
  Writer.bytes m.random
  Writer.opaque8 m.sessionId
  Writer.u16 m.cipherSuite
  Writer.u8 0
  writeExtensions m.extensions

def certificate : Parser Certificate := do
  let context ← Parser.opaque8
  let entries ← Parser.vec24 (Parser.many do
    let data ← Parser.opaque24
    let extensions ← Parser.opaque16
    pure { data, extensions : CertificateEntry })
  pure { context, entries }

def writeCertificate (m : Certificate) : Writer Unit := do
  Writer.opaque8 m.context
  Writer.prefixed 3 do
    for e in m.entries do
      Writer.opaque24 e.data
      Writer.opaque16 e.extensions

def certificateVerify : Parser CertificateVerify := do
  let scheme ← Parser.u16
  let signature ← Parser.opaque16
  pure { scheme, signature }

def writeCertificateVerify (m : CertificateVerify) : Writer Unit := do
  Writer.u16 m.scheme
  Writer.opaque16 m.signature

/-- A handshake message with its 4-byte header: type and 24-bit length. -/
def frame (typ : UInt8) (body : Writer Unit) : Except Alert ByteArray :=
  Writer.run do
    Writer.u8 typ
    Writer.prefixed 3 body

/-- The largest handshake message accepted from a peer. Bounds the reassembly buffer. -/
def maxMessageSize : Nat := 65536

structure RawMessage where
  typ  : UInt8
  body : ByteArray
  /-- The whole message, header included, as it enters the transcript. -/
  raw  : ByteArray

/-- Split complete messages off the front of `buf`; the rest is an incomplete message. -/
def splitMessages (buf : ByteArray) : Except Alert (Array RawMessage × ByteArray) :=
  go buf.size 0 #[]
where
  /-- Messages from `pos` on, at most `fuel` of them. -/
  go : Nat → Nat → Array RawMessage → Except Alert (Array RawMessage × ByteArray)
    | 0, pos, out => pure (out, buf.extract pos buf.size)
    | fuel + 1, pos, out =>
      if pos + 4 > buf.size then pure (out, buf.extract pos buf.size) else
      let len := (buf.get! (pos + 1)).toNat * 65536 + (buf.get! (pos + 2)).toNat * 256 +
        (buf.get! (pos + 3)).toNat
      if len > maxMessageSize then throw .decodeError
      else if pos + 4 + len > buf.size then pure (out, buf.extract pos buf.size)
      else go fuel (pos + 4 + len) (out.push
        ⟨buf.get! pos, buf.extract (pos + 4) (pos + 4 + len), buf.extract pos (pos + 4 + len)⟩)

end LeanTLS.Messages

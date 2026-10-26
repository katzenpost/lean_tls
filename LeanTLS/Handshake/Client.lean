/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import LeanTLS.Handshake.Common
import LeanTLS.X509

namespace LeanTLS.Handshake.Client

open LeanTLS.Messages
open LeanTLS.Wire
open LeanTLS.KeySchedule (TrafficSecrets handshakeSecret handshakeTraffic applicationTraffic masterSecret finishedData)
open Cryptlib.Util.Bytes (toVecN ofVector)

/-! # The client handshake

A 1-RTT TLS 1.3 handshake for QUIC that authenticates the server by a pinned
`SHA-256(SubjectPublicKeyInfo)` and an Ed25519 or ML-DSA-65 CertificateVerify. One key share is offered and
HelloRetryRequest is refused. The client sends no certificate.

The phases carry only what has been established so far. `Established` is the client's evidence
that the server is authenticated; its constructor is private to this module, which builds one only
after the pin and the signature have checked, and moves to `connected` only after the server's
Finished has too. -/

structure Config : Type where
  group  : Group := .x25519mlkem768
  suites : List Suite := cipherSuites
  alpn   : ByteArray
  /-- The QUIC transport parameters, already encoded. -/
  transportParams : ByteArray
  /-- `SHA-256(SubjectPublicKeyInfo)` of each acceptable server key. -/
  pins : List ByteArray
  /-- How the server may authenticate; ML-DSA-65 alone for post-quantum authentication. -/
  schemes : List Scheme := [.ed25519, .mldsa65]
  serverName : Option String := none

abbrev Config.share (cfg : Config) : KeyShare := cfg.group.keyShare

structure Established (cfg : Config) : Type where
  private mk ::
  suite : Suite
  alpn : ByteArray
  peerTransportParams : ByteArray
  spki : ByteArray
  pinned : KeySchedule.hash spki ∈ cfg.pins
  serverKey : AuthKey
  signedInput : ByteArray
  signature : ByteArray
  signatureValid : serverKey.verify signedInput signature = true

/-- Handshake keys and the transcript so far. -/
structure HsCtx where
  suite : Suite
  hs : ByteArray
  secrets : TrafficSecrets
  transcript : ByteArray

inductive Phase (cfg : Config) : Type where
  | waitServerHello (secret : cfg.share.ClientSecret) (transcript : ByteArray)
  | waitEncryptedExtensions (ctx : HsCtx)
  | waitCertificate (ctx : HsCtx) (alpn tps : ByteArray)
  | waitCertificateVerify (ctx : HsCtx) (alpn tps spki : ByteArray) (pinned : KeySchedule.hash spki ∈ cfg.pins)
      (key : AuthKey)
  | waitFinished (ctx : HsCtx) (est : Established cfg)
  | connected (est : Established cfg)
  | failed (alert : Alert)

structure State (cfg : Config) : Type where
  phase : Phase cfg
  buffers : Buffers := {}

def State.established? {cfg : Config} (s : State cfg) : Option (Established cfg) :=
  match s.phase with
  | .connected e => some e
  | _ => none

def clientHello (cfg : Config) (random share : ByteArray) : Except Alert ByteArray := do
  let mut exts := #[]
  if let some name := cfg.serverName then
    exts := exts.push (← ext ExtType.serverName (Writer.prefixed 2 do
      Writer.u8 0
      Writer.opaque16 name.toUTF8))
  exts := exts.push (← ext ExtType.supportedVersions (Writer.prefixed 1 (Writer.u16 tls13)))
  exts := exts.push (← ext ExtType.supportedGroups (Writer.prefixed 2 (Writer.u16 cfg.share.group)))
  exts := exts.push (← ext ExtType.signatureAlgorithms (Writer.prefixed 2
    (for s in cfg.schemes do Writer.u16 s.code)))
  exts := exts.push (← ext ExtType.keyShare (Writer.prefixed 2
    (writeKeyShareEntry { group := cfg.share.group, key := share })))
  exts := exts.push (← ext ExtType.alpn (writeAlpnList #[cfg.alpn]))
  exts := exts.push { typ := ExtType.quicTransportParameters, data := cfg.transportParams }
  frame HandshakeType.clientHello (writeClientHello
    { random, sessionId := ByteArray.empty, cipherSuites := (cfg.suites.map (·.id)).toArray,
      extensions := exts })

/-- Begin a handshake: the ClientHello, to send in Initial packets. -/
def start (cfg : Config) (seed : Vector UInt8 32) : Except Alert (State cfg × Array Output) := do
  let (secret, share) := cfg.share.clientGen (drawVec seed "key share" cfg.share.entropySize)
  let ch ← clientHello cfg (draw seed "client random" 32) (ofVector share)
  pure ({ phase := .waitServerHello secret ch }, #[.send .initial ch])

def onServerHello (cfg : Config) (secret : cfg.share.ClientSecret) (transcript : ByteArray)
    (m : RawMessage) : Except Alert (Phase cfg × Array Output) := do
  let sh ← Parser.run serverHello m.body
  if sh.random == helloRetryRandom then throw .handshakeFailure
  if sh.sessionId.size != 0 then throw .illegalParameter
  let suite ← require (cfg.suites.find? (·.id == sh.cipherSuite)) .illegalParameter
  let v ← decodeExt Parser.u16 (← require (find sh.extensions ExtType.supportedVersions) .missingExtension)
  if v != tls13 then throw .illegalParameter
  let e ← decodeExt keyShareEntry (← require (find sh.extensions ExtType.keyShare) .missingExtension)
  if e.group != cfg.share.group || e.key.size != cfg.share.serverShareSize then throw .illegalParameter
  let k ← require (cfg.share.clientFinish secret (toVecN _ e.key)) .illegalParameter
  let transcript := transcript ++ m.raw
  let hs := handshakeSecret (ofVector k)
  let ts := handshakeTraffic hs transcript
  pure (.waitEncryptedExtensions { suite, hs, secrets := ts, transcript },
    #[.install .handshake suite { read := ts.server, write := ts.client }])

def onEncryptedExtensions (cfg : Config) (ctx : HsCtx) (m : RawMessage) :
    Except Alert (Phase cfg × Array Output) := do
  let exts ← Parser.run extensions m.body
  let protos ← decodeExt alpnList (← require (find exts ExtType.alpn) .noApplicationProtocol)
  if protos.size != 1 || protos[0]! != cfg.alpn then throw .noApplicationProtocol
  let tps ← require (find exts ExtType.quicTransportParameters) .missingExtension
  pure (.waitCertificate { ctx with transcript := ctx.transcript ++ m.raw } cfg.alpn tps, #[])

def onCertificate (cfg : Config) (ctx : HsCtx) (alpn tps : ByteArray) (m : RawMessage) :
    Except Alert (Phase cfg × Array Output) := do
  let c ← Parser.run certificate m.body
  if c.context.size != 0 then throw .illegalParameter
  let entry ← require c.entries[0]? .badCertificate
  let leaf ← X509.parseLeaf entry.data
  let key ← require leaf.key .badCertificate
  unless cfg.schemes.contains key.scheme do throw .badCertificate
  let ctx := { ctx with transcript := ctx.transcript ++ m.raw }
  if h : KeySchedule.hash leaf.spki ∈ cfg.pins then
    pure (.waitCertificateVerify ctx alpn tps leaf.spki h key, #[])
  else throw .badCertificate

def onCertificateVerify (cfg : Config) (ctx : HsCtx) (alpn tps spki : ByteArray)
    (pinned : KeySchedule.hash spki ∈ cfg.pins) (key : AuthKey) (m : RawMessage) :
    Except Alert (Phase cfg × Array Output) := do
  let cv ← Parser.run certificateVerify m.body
  if cv.scheme != key.scheme.code then throw .illegalParameter
  let input := certVerifyInput true ctx.transcript
  if hv : key.verify input cv.signature = true then
    let est : Established cfg := ⟨ctx.suite, alpn, tps, spki, pinned, key, input, cv.signature, hv⟩
    pure (.waitFinished { ctx with transcript := ctx.transcript ++ m.raw } est, #[])
  else throw .decryptError

def onFinished (cfg : Config) (ctx : HsCtx) (est : Established cfg) (m : RawMessage) :
    Except Alert (Phase cfg × Array Output) := do
  unless ctEq m.body (finishedData ctx.secrets.server ctx.transcript) do throw .decryptError
  let transcript := ctx.transcript ++ m.raw
  let ap := applicationTraffic (masterSecret ctx.hs) transcript
  let fin ← frame HandshakeType.finished (Writer.bytes (finishedData ctx.secrets.client transcript))
  pure (.connected est,
    #[.send .handshake fin, .install .application ctx.suite { read := ap.server, write := ap.client }])

def handle (cfg : Config) (p : Phase cfg) (level : Level) (m : RawMessage) :
    Except Alert (Phase cfg × Array Output) :=
  match p, level with
  | .waitServerHello secret tr, .initial =>
    if m.typ == HandshakeType.serverHello then onServerHello cfg secret tr m else throw .unexpectedMessage
  | .waitEncryptedExtensions ctx, .handshake =>
    if m.typ == HandshakeType.encryptedExtensions then onEncryptedExtensions cfg ctx m
    else throw .unexpectedMessage
  | .waitCertificate ctx alpn tps, .handshake =>
    if m.typ == HandshakeType.certificate then onCertificate cfg ctx alpn tps m
    else throw .unexpectedMessage
  | .waitCertificateVerify ctx alpn tps spki h key, .handshake =>
    if m.typ == HandshakeType.certificateVerify then onCertificateVerify cfg ctx alpn tps spki h key m
    else throw .unexpectedMessage
  | .waitFinished ctx est, .handshake =>
    if m.typ == HandshakeType.finished then onFinished cfg ctx est m else throw .unexpectedMessage
  | .connected est, .application =>
    -- Session tickets are not used: no resumption.
    if m.typ == HandshakeType.newSessionTicket then pure (.connected est, #[])
    else throw .unexpectedMessage
  | _, _ => throw .unexpectedMessage

/-- CRYPTO stream bytes received at `level`, in order. -/
def recv {cfg : Config} (s : State cfg) (level : Level) (data : ByteArray) :
    Except Alert (State cfg × Array Output) := do
  if let .failed a := s.phase then throw a
  let (msgs, rest) ← splitMessages (s.buffers.get level ++ data)
  let mut phase := s.phase
  let mut out := #[]
  for m in msgs do
    let (p, o) ← handle cfg phase level m
    phase := p
    out := out ++ o
  pure ({ phase, buffers := s.buffers.set level rest }, out)

end LeanTLS.Handshake.Client

/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import LeanTLS.Handshake.Common
import LeanTLS.X509

namespace LeanTLS.Handshake.Server

open LeanTLS.Messages
open LeanTLS.Wire
open LeanTLS.KeySchedule
open Cryptlib.Util.Bytes (toVecN ofVector)

/-! # The server handshake

Answers a ClientHello offering its key share group, a cipher suite it supports, its signature
scheme and its ALPN protocol, with its whole first flight; then waits for the client's Finished.
The server authenticates with one certificate, Ed25519 or ML-DSA-65, and asks for none.

`Established` has a private constructor: this module builds one only once the client's Finished
has checked. -/

structure Config : Type where
  group  : Group := .x25519mlkem768
  suites : List Suite := cipherSuites
  alpn   : ByteArray
  transportParams : ByteArray
  /-- How the server authenticates. -/
  scheme : Scheme := .ed25519
  /-- The private key seed: Ed25519's (RFC 8032) or ML-DSA-65's ξ (FIPS 204). -/
  signingKey : Vector UInt8 32
  /-- DER, holding `signingKey`'s public key. -/
  certificate : ByteArray
  /-- ML-DSA's expansion of `signingKey`, made on first use and kept for later handshakes. -/
  mldsaKey : Thunk (Cryptlib.Primitives.Sign.FIPS204.Expanded MLDSA.mldsa65) :=
    Thunk.mk fun _ => Cryptlib.Primitives.Sign.FIPS204.expand _ signingKey
  mldsaKey_seed : mldsaKey.get.seed = signingKey := by rfl

abbrev Config.share (cfg : Config) : KeyShare := cfg.group.keyShare

/-- `cfg.scheme.sign cfg.signingKey`, signing ML-DSA with the kept expansion of the key. -/
def Config.sign (cfg : Config) (seed : Vector UInt8 32) (input : ByteArray) : Except Alert ByteArray :=
  match cfg.scheme with
  | .mldsa65 => (signResult (Cryptlib.Primitives.Sign.FIPS204.signExpanded _ cfg.mldsaKey.get input
      (mldsaState seed))).map (ofVector (n := mldsa65Sig.sigSize))
  | sch => sch.sign cfg.signingKey seed input

theorem Config.sign_eq (cfg : Config) (seed : Vector UInt8 32) (input : ByteArray) :
    cfg.sign seed input = cfg.scheme.sign cfg.signingKey seed input := by
  unfold Config.sign
  split
  · rename_i h
    rw [h, Cryptlib.Primitives.Sign.FIPS204.signExpanded_eq, cfg.mldsaKey_seed]
    simp only [Scheme.sign, mldsa65Sig, Cryptlib.Primitives.Sign.FIPS204.mldsa65Signature,
      Cryptlib.Primitives.Sign.FIPS204.scheme]
  · rfl

structure Established : Type where
  private mk ::
  suite : Suite
  alpn : ByteArray
  peerTransportParams : ByteArray
  clientFinished : ByteArray
  /-- The verify data the transcript and the client's handshake secret call for. -/
  expectedFinished : ByteArray
  finishedValid : clientFinished = expectedFinished

structure Pending where
  suite : Suite
  clientHandshake : ByteArray
  transcript : ByteArray
  peerTransportParams : ByteArray

inductive Phase : Type where
  | waitClientHello
  | waitFinished (p : Pending)
  | connected (est : Established)

structure State : Type where
  phase : Phase := .waitClientHello
  buffers : Buffers := {}

def State.established? (s : State) : Option Established :=
  match s.phase with
  | .connected e => some e
  | _ => none

def init : State := {}

def onClientHello (cfg : Config) (seed : Vector UInt8 32) (m : RawMessage) :
    Except Alert (Phase × Array Output) := do
  let ch ← Parser.run clientHello m.body
  -- RFC 9001 §8.4: QUIC has no middlebox compatibility mode.
  if ch.sessionId.size != 0 then throw .illegalParameter
  let versions ← decodeExt (Parser.vec8 u16List)
    (← require (find ch.extensions ExtType.supportedVersions) .missingExtension)
  unless versions.contains tls13 do throw .protocolVersion
  let suite ← require (cfg.suites.find? (ch.cipherSuites.contains ·.id)) .handshakeFailure
  let sigs ← decodeExt (Parser.vec16 u16List)
    (← require (find ch.extensions ExtType.signatureAlgorithms) .missingExtension)
  unless sigs.contains cfg.scheme.code do throw .handshakeFailure
  let protos ← decodeExt alpnList (← require (find ch.extensions ExtType.alpn) .noApplicationProtocol)
  unless protos.contains cfg.alpn do throw .noApplicationProtocol
  let tps ← require (find ch.extensions ExtType.quicTransportParameters) .missingExtension
  let shares ← decodeExt (Parser.vec16 (Parser.many keyShareEntry))
    (← require (find ch.extensions ExtType.keyShare) .missingExtension)
  let entry ← require (shares.find? (·.group == cfg.share.group)) .handshakeFailure
  if entry.key.size != cfg.share.clientShareSize then throw .illegalParameter
  let (myShare, k) ← require
    (cfg.share.serverRespond (drawVec seed "key share" cfg.share.entropySize) (toVecN _ entry.key))
    .illegalParameter
  let sh ← frame HandshakeType.serverHello (writeServerHello
    { random := draw seed "server random" 32, sessionId := ByteArray.empty, cipherSuite := suite.id,
      extensions := #[
        ← ext ExtType.supportedVersions (Writer.u16 tls13),
        ← ext ExtType.keyShare (writeKeyShareEntry { group := cfg.share.group, key := ofVector myShare })] })
  let transcript := m.raw ++ sh
  let hs := handshakeSecret (ofVector k)
  let hts := handshakeTraffic hs transcript
  let ee ← frame HandshakeType.encryptedExtensions (writeExtensions #[
    ← ext ExtType.alpn (writeAlpnList #[cfg.alpn]),
    { typ := ExtType.quicTransportParameters, data := cfg.transportParams }])
  let cert ← frame HandshakeType.certificate
    (writeCertificate ⟨ByteArray.empty, #[⟨cfg.certificate, ByteArray.empty⟩]⟩)
  let transcript := transcript ++ ee ++ cert
  let sig ← cfg.sign seed (certVerifyInput true transcript)
  let cv ← frame HandshakeType.certificateVerify
    (writeCertificateVerify { scheme := cfg.scheme.code, signature := sig })
  let transcript := transcript ++ cv
  let fin ← frame HandshakeType.finished (Writer.bytes (finishedData hts.server transcript))
  let transcript := transcript ++ fin
  let ap := applicationTraffic (masterSecret hs) transcript
  pure (.waitFinished { suite, clientHandshake := hts.client, transcript, peerTransportParams := tps },
    #[.send .initial sh,
      .install .handshake suite { read := hts.client, write := hts.server },
      .send .handshake (ee ++ cert ++ cv ++ fin),
      .install .application suite { read := ap.client, write := ap.server }])

def onFinished (cfg : Config) (p : Pending) (m : RawMessage) :
    Except Alert (Phase × Array Output) := do
  let expected := finishedData p.clientHandshake p.transcript
  if h : ctEq m.body expected = true then
    pure (.connected ⟨p.suite, cfg.alpn, p.peerTransportParams, m.body, expected,
      (Cryptlib.Util.ConstantTime.ctEq_iff _ _).mp h⟩, #[])
  else throw .decryptError

/-- CRYPTO stream bytes received at `level`, in order. `seed` is the connection's entropy. -/
def recv (cfg : Config) (seed : Vector UInt8 32) (s : State) (level : Level) (data : ByteArray) :
    Except Alert (State × Array Output) := do
  let (msgs, rest) ← splitMessages (s.buffers.get level ++ data)
  let mut phase := s.phase
  let mut out := #[]
  for m in msgs do
    let (p, o) ← match phase, level with
      | .waitClientHello, .initial =>
        if m.typ == HandshakeType.clientHello then onClientHello cfg seed m else throw .unexpectedMessage
      | .waitFinished p, .handshake =>
        if m.typ == HandshakeType.finished then onFinished cfg p m else throw .unexpectedMessage
      | _, _ => throw .unexpectedMessage
    phase := p
    out := out ++ o
  pure ({ phase, buffers := s.buffers.set level rest }, out)

end LeanTLS.Handshake.Server

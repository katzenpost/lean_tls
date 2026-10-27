/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import LeanTLSBench.Fixtures
import LeanBench

/-! # The handshake's parts as lean_tls calls them: key shares, CertificateVerify signing and
checking, certificate parsing, the transcript hash, the key schedule and message splitting

Transcripts and flights are those of a real handshake. Inputs are read from refs so the compiler
cannot hoist the work out of the timed action. -/

namespace LeanTLSBench.Pieces

open LeanTLS
open LeanTLS.Handshake
open LeanTLS.KeySchedule
open Cryptlib.Util.Bytes (ofVector)

private def cfg : LeanBench.BenchConfig := { suite := some "tls", samples := 10, warmup := 1 }

def keyShareBenches (g : Group) : IO (Array LeanBench.Bench) := do
  let ks := g.keyShare
  let n := ks.name
  let ec ← IO.mkRef (Vector.replicate ks.entropySize (0 : UInt8))
  let es ← IO.mkRef (Vector.replicate ks.entropySize (0 : UInt8))
  let fresh : IO Unit := do
    let a ← IO.getRandomBytes ks.entropySize.toUSize
    let b ← IO.getRandomBytes ks.entropySize.toUSize
    ec.set (Vector.ofFn fun i => a[i.val]!)
    es.set (Vector.ofFn fun i => b[i.val]!)
  let gen ← IO.mkRef (none : Option (ks.ClientSecret × Vector UInt8 ks.clientShareSize))
  let resp ← IO.mkRef (none : Option (Vector UInt8 ks.serverShareSize × Vector UInt8 ks.secretSize))
  let fin ← IO.mkRef (none : Option (Vector UInt8 ks.secretSize))
  let prepare : IO Unit := do
    fresh
    let g := ks.clientGen (← ec.get)
    gen.set (some g)
    resp.set (ks.serverRespond (← es.get) g.2)
  pure #[
    { name := s!"tls key share {n} client generate", config := cfg, beforeEach? := some fresh
      action := do gen.set (some (ks.clientGen (← ec.get))) },
    { name := s!"tls key share {n} server respond", config := cfg, beforeEach? := some prepare
      action := do
        let some (_, share) ← gen.get | throw (IO.userError "no share")
        resp.set (ks.serverRespond (← es.get) share) },
    { name := s!"tls key share {n} client finish", config := cfg, beforeEach? := some prepare
      action := do
        let some (sk, _) ← gen.get | throw (IO.userError "no share")
        let some (ct, _) ← resp.get | throw (IO.userError "server refused the share")
        fin.set (ks.clientFinish sk ct) }]

/-- Signing, verifying and certificate handling for one scheme, on the transcript of a real
handshake. -/
def authBenches (sch : Scheme) (name : String) : IO (Array LeanBench.Bench) := do
  let (scfg, pin) ← server .x25519mlkem768 sch
  let ccfg := client .x25519mlkem768 sch pin
  let (c, o0) ← orFail "start" (Client.start ccfg (← randomSeed))
  let (s, o1) ← orFail "server" (toServer scfg (← randomSeed) Server.init (sends o0))
  let .waitFinished p := s.phase | throw (IO.userError "server not waiting for Finished")
  let flight := (sends o1).filter (·.1 == .handshake) |>.foldl (fun b (_, d) => b ++ d) ByteArray.empty
  discard <| orFail "client" (toClient c (sends o1))
  let key := sch.authKey scfg.signingKey
  let sk ← IO.mkRef scfg.signingKey
  let seed ← IO.mkRef (← randomSeed)
  let input ← IO.mkRef (certVerifyInput true p.transcript)
  let sig ← IO.mkRef ByteArray.empty
  let keyRef ← IO.mkRef key
  let cert ← IO.mkRef scfg.certificate
  let transcript ← IO.mkRef p.transcript
  let flightRef ← IO.mkRef flight
  let ok ← IO.mkRef false
  let outB ← IO.mkRef ByteArray.empty
  let out ← IO.mkRef (none : Option AuthKey)
  let msgs ← IO.mkRef (0 : Nat)
  let theSig ← orFail "sign" (sch.sign scfg.signingKey (← randomSeed) (certVerifyInput true p.transcript))
  sig.set theSig
  let tlen := p.transcript.size
  pure #[
    { name := s!"tls sign CertificateVerify {name}", config := cfg
      beforeEach? := some do seed.set (← randomSeed)
      action := do outB.set (← orFail "sign" (sch.sign (← sk.get) (← seed.get) (← input.get))) },
    { name := s!"tls verify CertificateVerify {name}", config := cfg
      action := do ok.set ((← keyRef.get).verify (← input.get) (← sig.get)) },
    { name := s!"tls public key from seed {name}", config := cfg
      action := do out.set (some (sch.authKey (← sk.get))) },
    { name := s!"tls parse certificate {name} ({scfg.certificate.size}B)", config := cfg
      action := do
        match X509.parseLeaf (← cert.get) with
        | .ok leaf => outB.set (KeySchedule.hash leaf.spki)
        | .error a => throw (IO.userError s!"parse: {repr a}") },
    { name := s!"tls transcript hash {name} ({tlen}B)", config := cfg
      action := do outB.set (hash (← transcript.get)) },
    { name := s!"tls certVerifyInput {name} ({tlen}B transcript)", config := cfg
      action := do outB.set (certVerifyInput true (← transcript.get)) },
    { name := s!"tls key schedule {name} ({tlen}B transcript)", config := cfg
      action := do
        let tr ← transcript.get
        let hs := handshakeSecret (ofVector (← seed.get))
        let hts := handshakeTraffic hs tr
        let sf := finishedData hts.server tr
        let ap := applicationTraffic (masterSecret hs) tr
        let cf := finishedData hts.client tr
        outB.set (sf ++ cf ++ ap.client ++ ap.server) },
    { name := s!"tls split server flight {name} ({flight.size}B)", config := cfg
      action := do
        let (ms, _) ← orFail "split" (Messages.splitMessages (← flightRef.get))
        msgs.set ms.size }]

def benches : IO (Array LeanBench.Bench) := do
  let mut bs := #[]
  for g in [Group.x25519mlkem768, .mlkem768, .x25519] do
    bs := bs ++ (← keyShareBenches g)
  bs := bs ++ (← authBenches .mldsa65 "ML-DSA-65")
  bs := bs ++ (← authBenches .ed25519 "Ed25519")
  let secret ← IO.mkRef (bytes 32)
  let empty ← IO.mkRef ByteArray.empty
  let out ← IO.mkRef ByteArray.empty
  bs := bs.push { name := "tls hkdf extract", config := cfg
                  action := do out.set (hkdfExtract (← secret.get) (← secret.get)) }
  bs := bs.push { name := "tls hkdf expandLabel 32B", config := cfg
                  action := do out.set (expandLabel (← secret.get) "c hs traffic" (← secret.get) 32) }
  bs := bs.push { name := "tls key schedule, empty transcript", config := cfg
                  action := do
                    let tr ← empty.get
                    let hs := handshakeSecret (← secret.get)
                    let hts := handshakeTraffic hs tr
                    let sf := finishedData hts.server tr
                    let ap := applicationTraffic (masterSecret hs) tr
                    let cf := finishedData hts.client tr
                    out.set (sf ++ cf ++ ap.client ++ ap.server) }
  pure bs

end LeanTLSBench.Pieces

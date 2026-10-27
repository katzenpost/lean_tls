/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import LeanTLSBench.Fixtures
import LeanBench

/-! # Packet protection with the negotiated suites

lean_tls has no TLS record layer: QUIC protects packets itself, with the suite's AEAD and header
protection and the keys `quicKeys` derives (RFC 9001 §5). These are what lean_quic calls per packet,
measured on a full-size 1200-byte packet and a 16 KiB payload. -/

namespace LeanTLSBench.Packet

open LeanTLS
open LeanTLS.KeySchedule

private def cfg : LeanBench.BenchConfig := { suite := some "tls", samples := 10, warmup := 1 }

def sizes : List (Nat × String) := [(1200, "1200B"), (16384, "16KiB")]

def suiteName : Suite → String
  | .chacha20poly1305 => "ChaCha20-Poly1305"
  | .aes128gcm => "AES-128-GCM"

def benches : IO (Array LeanBench.Bench) := do
  let mut bs := #[]
  let secret ← IO.mkRef (bytes 32)
  for s in [Suite.chacha20poly1305, .aes128gcm] do
    let cs := s.cipherSuite
    let n := suiteName s
    let keyLen := cs.aead.keySize
    let pk := quicKeys (bytes 32) keyLen
    let keysOut ← IO.mkRef pk
    let keyBytes ← IO.mkRef pk.key
    let key ← IO.mkRef (cs.key pk.key)
    let hp ← IO.mkRef pk.hp
    let nonce ← IO.mkRef (Vector.replicate 12 (9 : UInt8))
    let sample ← IO.mkRef (Vector.replicate 16 (5 : UInt8))
    let ad ← IO.mkRef (bytes 20)
    let mask ← IO.mkRef (Vector.replicate 5 (0 : UInt8))
    let out ← IO.mkRef ByteArray.empty
    let opened ← IO.mkRef (none : Option ByteArray)
    bs := bs.push { name := s!"tls quic packet keys {n}", config := cfg
                    action := do keysOut.set (quicKeys (← secret.get) keyLen) }
    bs := bs.push { name := s!"tls aead key setup {n}", config := cfg
                    action := do key.set (cs.key (← keyBytes.get)) }
    bs := bs.push { name := s!"tls header protection mask {n}", config := cfg
                    action := do mask.set (cs.hpMask (← hp.get) (← sample.get)) }
    for (size, label) in sizes do
      let pt ← IO.mkRef (bytes size)
      let ct ← IO.mkRef (cs.aead.encrypt (cs.key pk.key) (cs.nonce (Vector.replicate 12 9)) (bytes 20) (bytes size))
      bs := bs.push { name := s!"tls seal {n} {label}", config := cfg
                      action := do
                        out.set (cs.aead.encrypt (← key.get) (cs.nonce (← nonce.get)) (← ad.get) (← pt.get)) }
      bs := bs.push { name := s!"tls open {n} {label}", config := cfg
                      action := do
                        let r := cs.aead.decrypt (← key.get) (cs.nonce (← nonce.get)) (← ad.get) (← ct.get)
                        if r.isNone then throw (IO.userError "open failed")
                        opened.set r }
  pure bs

end LeanTLSBench.Packet

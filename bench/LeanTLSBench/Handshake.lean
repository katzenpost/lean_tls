/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import LeanTLSBench.Fixtures
import LeanBench

/-! # Handshake benchmarks: the whole in-process handshake, and each side's step on its own

Every sample draws fresh connection seeds, so the key shares, signatures and ML-DSA's rejection
sampling vary as they would between connections. The messages a step consumes are produced in
`beforeEach`, outside the timed region, and read from refs inside it. -/

namespace LeanTLSBench.Handshake

open LeanTLS
open LeanTLS.Handshake

private def cfg : LeanBench.BenchConfig := { suite := some "tls", samples := 10, warmup := 1 }

def schemeName : Scheme → String
  | .ed25519 => "Ed25519"
  | .mldsa65 => "ML-DSA-65"

/-- The pairs measured: the deployed X25519MLKEM768 with either signature, and plain X25519. -/
def combos : List (Group × Scheme) :=
  [(.x25519mlkem768, .mldsa65), (.x25519mlkem768, .ed25519), (.x25519, .mldsa65), (.x25519, .ed25519)]

def benches : IO (Array LeanBench.Bench) := do
  let mut bs := #[]
  for g in [Group.x25519mlkem768, .x25519] do
    let (_, pin) ← server g .ed25519
    let ccfg := client g .ed25519 pin
    let seedA ← IO.mkRef (← randomSeed)
    let out ← IO.mkRef (#[] : Array Output)
    bs := bs.push { name := s!"tls client hello {g.keyShare.name}", config := cfg
                    beforeEach? := some do seedA.set (← randomSeed)
                    action := do out.set (← orFail "start" (Client.start ccfg (← seedA.get))).2 }
  for (g, sch) in combos do
    let label := s!"{g.keyShare.name} {schemeName sch}"
    let (scfg, pin) ← server g sch
    let ccfg := client g sch pin
    let seedA ← IO.mkRef (← randomSeed)
    let seedB ← IO.mkRef (← randomSeed)
    let fresh : IO Unit := do
      seedA.set (← randomSeed)
      seedB.set (← randomSeed)
    let hello ← IO.mkRef (#[] : Array (Level × ByteArray))
    let flight ← IO.mkRef (#[] : Array (Level × ByteArray))
    let finished ← IO.mkRef (#[] : Array (Level × ByteArray))
    let c0 ← IO.mkRef (none : Option (Client.State ccfg))
    let s1 ← IO.mkRef (Server.init)
    let out ← IO.mkRef (#[] : Array Output)
    let done ← IO.mkRef false
    let toFlight : IO Unit := do
      fresh
      let (c, o0) ← orFail "start" (Client.start ccfg (← seedA.get))
      c0.set (some c)
      hello.set (sends o0)
      let (s, o1) ← orFail "server" (toServer scfg (← seedB.get) Server.init (sends o0))
      s1.set s
      flight.set (sends o1)
    bs := bs.push { name := s!"tls handshake {label}", config := cfg, beforeEach? := some fresh
                    action := do
                      let (c, s) ← orFail "handshake" (handshake ccfg scfg (← seedA.get) (← seedB.get))
                      done.set (c.established?.isSome && s.established?.isSome) }
    bs := bs.push { name := s!"tls server ClientHello to flight {label}", config := cfg
                    beforeEach? := some toFlight
                    action := do
                      out.set (← orFail "server" (toServer scfg (← seedB.get) Server.init (← hello.get))).2 }
    bs := bs.push { name := s!"tls client server flight to Finished {label}", config := cfg
                    beforeEach? := some toFlight
                    action := do
                      let some c ← c0.get | throw (IO.userError "no client state")
                      let (c', o) ← orFail "client" (toClient c (← flight.get))
                      done.set c'.established?.isSome
                      out.set o }
    bs := bs.push { name := s!"tls server client Finished {label}", config := cfg
                    beforeEach? := some do
                      toFlight
                      let some c ← c0.get | throw (IO.userError "no client state")
                      finished.set (sends (← orFail "client" (toClient c (← flight.get))).2)
                    action := do
                      let (s, _) ← orFail "server" (toServer scfg (← seedB.get) (← s1.get) (← finished.get))
                      done.set s.established?.isSome }
  pure bs

end LeanTLSBench.Handshake

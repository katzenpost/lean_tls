/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import LeanTLS

/-! # What the benchmarks share: seeds, certificates, configurations and a driver that hands each
side's CRYPTO stream bytes straight to the other -/

namespace LeanTLSBench

open LeanTLS
open LeanTLS.Handshake
open Cryptlib.Util.Bytes (ofVector)

def randomSeed : IO (Vector UInt8 32) := do
  let bs ← IO.getRandomBytes 32
  pure (Vector.ofFn fun i : Fin 32 => bs[i.val]!)

def bytes (n : Nat) : ByteArray := ByteArray.mk (Array.ofFn fun (i : Fin n) => (i.val * 7 % 251).toUInt8)

def h3 : ByteArray := "h3".toUTF8

/-- A server's certificate for `scheme`, its configuration and the pin a client needs. -/
def server (group : Group) (scheme : Scheme) : IO (Server.Config × ByteArray) := do
  let sk ← randomSeed
  let cert ← match X509.certificateFor scheme (ofVector sk) (ofVector (← randomSeed))
      ⟨Array.replicate 16 7⟩ 1761433200 1761436800 with
    | .ok c => pure c
    | .error a => throw (IO.userError s!"certificate: {repr a}")
  let pin ← match X509.parseLeaf cert with
    | .ok leaf => pure (KeySchedule.hash leaf.spki)
    | .error a => throw (IO.userError s!"parse certificate: {repr a}")
  pure ({ group, alpn := h3, transportParams := bytes 64, scheme, signingKey := sk, certificate := cert }, pin)

def client (group : Group) (scheme : Scheme) (pin : ByteArray) : Client.Config :=
  { group, alpn := h3, transportParams := bytes 64, pins := [pin], schemes := [scheme] }

def sends (out : Array Output) : Array (Level × ByteArray) :=
  out.filterMap fun | .send l d => some (l, d) | _ => none

def toServer (cfg : Server.Config) (seed : Vector UInt8 32) (s : Server.State)
    (msgs : Array (Level × ByteArray)) : Except Alert (Server.State × Array Output) := do
  let mut st := s
  let mut out := #[]
  for (l, d) in msgs do
    let (st', o) ← Server.recv cfg seed st l d
    st := st'
    out := out ++ o
  pure (st, out)

def toClient {cfg : Client.Config} (s : Client.State cfg) (msgs : Array (Level × ByteArray)) :
    Except Alert (Client.State cfg × Array Output) := do
  let mut st := s
  let mut out := #[]
  for (l, d) in msgs do
    let (st', o) ← Client.recv st l d
    st := st'
    out := out ++ o
  pure (st, out)

/-- The whole handshake; both sides must end connected. -/
def handshake (ccfg : Client.Config) (scfg : Server.Config) (seedA seedB : Vector UInt8 32) :
    Except Alert (Client.State ccfg × Server.State) := do
  let (c0, o0) ← Client.start ccfg seedA
  let (s1, o1) ← toServer scfg seedB Server.init (sends o0)
  let (c1, o2) ← toClient c0 (sends o1)
  let (s2, _) ← toServer scfg seedB s1 (sends o2)
  if c1.established?.isNone || s2.established?.isNone then throw .internalError
  pure (c1, s2)

def orFail {α : Type} (what : String) : Except Alert α → IO α
  | .ok a => pure a
  | .error a => throw (IO.userError s!"{what}: {repr a}")

end LeanTLSBench

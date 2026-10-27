/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import LeanTLSBench.Handshake
import LeanTLSBench.Pieces
import LeanTLSBench.Packet

/-! # Benchmark driver -/

def main (args : List String) : IO UInt32 := do
  (← LeanTLSBench.Handshake.benches).forM LeanBench.register
  (← LeanTLSBench.Pieces.benches).forM LeanBench.register
  (← LeanTLSBench.Packet.benches).forM LeanBench.register
  LeanBench.runMain args

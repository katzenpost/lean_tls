/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import LeanTLS.KeyShare
import LeanTLS.KeySchedule

namespace LeanTLS.Agreement

open LeanTLS.KeySchedule
open Cryptlib.Util.Bytes (ofVector)

/-! # Both sides derive the same traffic secrets

The key schedule as each side runs it after the key exchange: the server from the client's share
and its own entropy, the client from its secret and the server's share. Both hash the same
transcripts, through ServerHello for the handshake secrets and through the server's Finished for
the application secrets. `keys_agree`: when the key exchange is `Reliable` and the server accepts
the client's share, the client derives exactly the server's secrets. -/

/-- The server's share, handshake and application traffic secrets. -/
def serverKeys (A : KeyShare) (es : Vector UInt8 A.entropySize)
    (share : Vector UInt8 A.clientShareSize) (thHello thFinished : ByteArray) :
    Option (Vector UInt8 A.serverShareSize × TrafficSecrets × TrafficSecrets) := do
  let (s, k) ← A.serverRespond es share
  let hs := handshakeSecret (ofVector k)
  pure (s, handshakeTraffic hs thHello, applicationTraffic (masterSecret hs) thFinished)

/-- The client's handshake and application traffic secrets. -/
def clientKeys (A : KeyShare) (cs : A.ClientSecret) (share : Vector UInt8 A.serverShareSize)
    (thHello thFinished : ByteArray) : Option (TrafficSecrets × TrafficSecrets) := do
  let k ← A.clientFinish cs share
  let hs := handshakeSecret (ofVector k)
  pure (handshakeTraffic hs thHello, applicationTraffic (masterSecret hs) thFinished)

theorem keys_agree (A : KeyShare) (ec es : Vector UInt8 A.entropySize) (h : A.Reliable ec es)
    {thHello thFinished : ByteArray} {s hts ats}
    (hs : serverKeys A es (A.clientGen ec).2 thHello thFinished = some (s, hts, ats)) :
    clientKeys A (A.clientGen ec).1 s thHello thFinished = some (hts, ats) := by
  simp only [serverKeys, bind, Option.bind] at hs
  split at hs
  · contradiction
  · rename_i r hr
    simp only [pure, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl, rfl⟩ := hs
    simp [clientKeys, A.agree ec es h r.1 r.2 hr]

end LeanTLS.Agreement

/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import LeanTLS.Alert

namespace LeanTLS.Wire

/-! # The TLS presentation language on the wire

Big-endian integers and length-prefixed vectors (RFC 8446 §3). A parser reads one input buffer
between a cursor and a limit; a length-prefixed vector narrows the limit, and its body must end
exactly at it. Every failure is `decodeError`. Writers fail instead of emitting a length that does
not fit its prefix. -/

structure Cursor where
  pos   : Nat
  limit : Nat

abbrev Parser := ReaderT ByteArray (StateT Cursor (Except Alert))

namespace Parser

def fail {α : Type} : Parser α := throw .decodeError

def remaining : Parser Nat := do
  let c ← get
  pure (c.limit - c.pos)

def atEnd : Parser Bool := do pure ((← remaining) == 0)

def bytes (n : Nat) : Parser ByteArray := do
  let b ← read
  let c ← get
  if c.pos + n ≤ c.limit then
    set { c with pos := c.pos + n }
    pure (b.extract c.pos (c.pos + n))
  else fail

def u8 : Parser UInt8 := do
  let b ← read
  let c ← get
  if c.pos < c.limit then
    set { c with pos := c.pos + 1 }
    pure (b.get! c.pos)
  else fail

def uN (n : Nat) : Parser Nat := do
  let b ← bytes n
  pure (b.foldl (fun acc x => acc * 256 + x.toNat) 0)

def u16 : Parser Nat := uN 2
def u24 : Parser Nat := uN 3
def u32 : Parser Nat := uN 4

/-- Run `p` on the next `n` bytes; it must consume all of them. -/
def sub {α : Type} (n : Nat) (p : Parser α) : Parser α := do
  let c ← get
  if c.pos + n ≤ c.limit then
    set { c with limit := c.pos + n }
    let a ← p
    let c' ← get
    if c'.pos == c.pos + n then
      set { c' with limit := c.limit }
      pure a
    else fail
  else fail

def vec8 {α : Type} (p : Parser α) : Parser α := do sub (← uN 1) p
def vec16 {α : Type} (p : Parser α) : Parser α := do sub (← u16) p
def vec24 {α : Type} (p : Parser α) : Parser α := do sub (← u24) p

def opaque8 : Parser ByteArray := vec8 (do bytes (← remaining))
def opaque16 : Parser ByteArray := vec16 (do bytes (← remaining))
def opaque24 : Parser ByteArray := vec24 (do bytes (← remaining))

/-- Items until the limit. Each must consume input, so at most `remaining` iterations. -/
def many {α : Type} (p : Parser α) : Parser (Array α) := do
  let mut out := #[]
  for _ in [0:(← remaining)] do
    if ← atEnd then break
    let before := (← get).pos
    out := out.push (← p)
    if (← get).pos == before then fail
  unless ← atEnd do fail
  pure out

def run {α : Type} (p : Parser α) (b : ByteArray) : Except Alert α := do
  let (a, c) ← (p b).run ⟨0, b.size⟩
  if c.pos == b.size then pure a else throw .decodeError

end Parser

abbrev Writer := StateT ByteArray (Except Alert)

namespace Writer

def bytes (b : ByteArray) : Writer Unit := modify (· ++ b)

def uN (n v : Nat) : Writer Unit := do
  if v < 256 ^ n then
    bytes ⟨Array.ofFn fun i : Fin n => UInt8.ofNat (v >>> (8 * (n - 1 - i.val)))⟩
  else throw .internalError

def u8 (v : UInt8) : Writer Unit := modify (·.push v)
def u16 (v : Nat) : Writer Unit := uN 2 v
def u24 (v : Nat) : Writer Unit := uN 3 v
def u32 (v : Nat) : Writer Unit := uN 4 v

/-- Write `w`'s output behind an `n`-byte length. -/
def prefixed (n : Nat) (w : Writer Unit) : Writer Unit := do
  let body ← match StateT.run w ByteArray.empty with
    | .ok ((), b) => pure b
    | .error e => throw e
  uN n body.size
  bytes body

def opaque8 (b : ByteArray) : Writer Unit := prefixed 1 (bytes b)
def opaque16 (b : ByteArray) : Writer Unit := prefixed 2 (bytes b)
def opaque24 (b : ByteArray) : Writer Unit := prefixed 3 (bytes b)

def run (w : Writer Unit) : Except Alert ByteArray := do
  let ((), b) ← StateT.run w ByteArray.empty
  pure b

end Writer

def u16be (v : Nat) : ByteArray := ⟨#[UInt8.ofNat (v >>> 8), UInt8.ofNat v]⟩

end LeanTLS.Wire

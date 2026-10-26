/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import LeanTLS.Wire

namespace LeanTLS.Wire

/-! # Parsers read what writers write

`Writes w out`: the writer appends exactly `out`. `Reads p x out`: wherever `out` sits in the input
at the cursor, the parser returns `x` and moves past it, whatever follows before the limit.
`ReadsAll` is the same for parsers that read up to the limit (vector bodies, `many`), when `out`
ends exactly there. The combinators carry these over, so a message's round trip is assembled from
its fields'. -/

variable {α β : Type}

/-! ## Running parsers and writers -/

namespace Parser

theorem bind_eq (p : Parser α) (q : α → Parser β) (B : ByteArray) (c : Cursor) :
    (p >>= q) B c = match p B c with | .ok (a, c') => q a B c' | .error e => .error e := by
  show Except.bind (p B c) _ = _
  rcases p B c with e | ⟨a, c'⟩ <;> rfl

theorem read_eq (B : ByteArray) (c : Cursor) : (read : Parser ByteArray) B c = .ok (B, c) := rfl
theorem get_eq (B : ByteArray) (c : Cursor) : (get : Parser Cursor) B c = .ok (c, c) := rfl
theorem set_eq (B : ByteArray) (c c' : Cursor) : (set c' : Parser PUnit) B c = .ok (⟨⟩, c') := rfl
theorem pure_eq (x : α) (B : ByteArray) (c : Cursor) : (pure x : Parser α) B c = .ok (x, c) := rfl
theorem fail_eq (B : ByteArray) (c : Cursor) : (fail : Parser α) B c = .error .decodeError := rfl
theorem throw_eq (e : Alert) (B : ByteArray) (c : Cursor) : (throw e : Parser α) B c = .error e := rfl
theorem ite_eq (q : Prop) [Decidable q] (x y : Parser α) (B : ByteArray) (c : Cursor) :
    (if q then x else y) B c = if q then x B c else y B c := by split <;> rfl

theorem remaining_eq (B : ByteArray) (c : Cursor) : remaining B c = .ok (c.limit - c.pos, c) := rfl

theorem atEnd_eq (B : ByteArray) (c : Cursor) : atEnd B c = .ok (c.limit - c.pos == 0, c) := rfl

theorem bytes_eq (n : Nat) (B : ByteArray) (c : Cursor) :
    bytes n B c = if c.pos + n ≤ c.limit then
      .ok (B.extract c.pos (c.pos + n), { c with pos := c.pos + n }) else .error .decodeError := by
  simp only [bytes, bind_eq, read_eq, get_eq, ite_eq, set_eq, pure_eq, fail_eq]

theorem u8_eq (B : ByteArray) (c : Cursor) :
    u8 B c = if c.pos < c.limit then .ok (B.get! c.pos, { c with pos := c.pos + 1 })
      else .error .decodeError := by
  simp only [u8, bind_eq, read_eq, get_eq, ite_eq, set_eq, pure_eq, fail_eq]

theorem sub_eq (n : Nat) (p : Parser α) (B : ByteArray) (c : Cursor) :
    sub n p B c = if c.pos + n ≤ c.limit then
      (match p B { c with limit := c.pos + n } with
       | .ok (a, c') => if c'.pos == c.pos + n then .ok (a, { c' with limit := c.limit })
                        else .error .decodeError
       | .error e => .error e)
    else .error .decodeError := by
  simp only [sub, bind_eq, get_eq, ite_eq, set_eq, pure_eq, fail_eq]

end Parser

namespace Writer

theorem bind_eq (w : Writer α) (v : α → Writer β) (s : ByteArray) :
    (w >>= v) s = match w s with | .ok (a, s') => v a s' | .error e => .error e := by
  show Except.bind (w s) _ = _
  rcases w s with e | ⟨a, s'⟩ <;> rfl

theorem pure_eq (x : α) (s : ByteArray) : (pure x : Writer α) s = .ok (x, s) := rfl
theorem bytes_eq (b s : ByteArray) : bytes b s = .ok ((), s ++ b) := rfl
theorem u8_eq (v : UInt8) (s : ByteArray) : u8 v s = .ok ((), s.push v) := rfl
theorem throw_eq (e : Alert) (s : ByteArray) : (throw e : Writer α) s = .error e := rfl
theorem ite_eq (q : Prop) [Decidable q] (x y : Writer α) (s : ByteArray) :
    (if q then x else y) s = if q then x s else y s := by split <;> rfl

end Writer

/-! ## Big-endian integers -/

/-- What `Writer.uN n v` writes. -/
def beBytes (n v : Nat) : ByteArray :=
  ⟨Array.ofFn fun i : Fin n => UInt8.ofNat (v >>> (8 * (n - 1 - i.val)))⟩

@[simp] theorem size_beBytes (n v : Nat) : (beBytes n v).size = n := by
  simp [beBytes, ByteArray.size]

def decodeBE (b : ByteArray) : Nat := b.data.foldl (fun acc x => acc * 256 + x.toNat) 0

theorem decodeBE_beBytes : ∀ n v : Nat, decodeBE (beBytes n v) = v % 256 ^ n
  | 0, v => by simp [decodeBE, beBytes, Nat.mod_one]
  | n + 1, v => by
    have ih := decodeBE_beBytes n (v >>> 8)
    have split : (beBytes (n + 1) v).data.toList =
        (beBytes n (v >>> 8)).data.toList ++ [UInt8.ofNat v] := by
      simp only [beBytes, Array.toList_ofFn, List.ofFn_succ_last]
      congr 1
      · congr 1
        funext i
        congr 1
        rw [← Nat.shiftRight_add]
        congr 1
        simp only [Fin.coe_castSucc]
        have := i.isLt
        omega
      · simp
    simp only [decodeBE, ← Array.foldl_toList] at ih ⊢
    rw [split, List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil, Nat.shiftRight_eq_div_pow]
    have : (UInt8.ofNat v).toNat = v % 256 := by simp
    rw [this, show (2 : Nat) ^ 8 = 256 by rfl, Nat.pow_succ', Nat.mod_mul]
    omega

theorem Writer.uN_eq (n v : Nat) (s : ByteArray) (hv : v < 256 ^ n) :
    Writer.uN n v s = .ok ((), s ++ beBytes n v) := by
  simp [Writer.uN, hv, Writer.bytes_eq, beBytes]

/-! ## Writers -/

def Writes (w : Writer Unit) (out : ByteArray) : Prop := ∀ s, w s = .ok ((), s ++ out)

namespace Writes

theorem det {w : Writer Unit} {o o' : ByteArray} (h : Writes w o) (h' : Writes w o') : o = o' := by
  have := (h ByteArray.empty).symm.trans (h' ByteArray.empty)
  simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at this
  simpa [ByteArray.empty_append] using this

theorem run {w : Writer Unit} {o : ByteArray} (h : Writes w o) : Writer.run w = .ok o := by
  show Except.bind (w ByteArray.empty) _ = _
  rw [h]
  simp [Except.bind, ByteArray.empty_append, pure, Except.pure]

theorem pure : Writes (Pure.pure ()) ByteArray.empty := fun s => by
  rw [Writer.pure_eq, ByteArray.append_empty]

theorem bind {w v : Writer Unit} {o o' : ByteArray} (h : Writes w o) (h' : Writes v o') :
    Writes (w >>= fun _ => v) (o ++ o') := fun s => by
  rw [Writer.bind_eq, h s]
  simp only
  rw [h' (s ++ o), ByteArray.append_assoc]

theorem bytes (b : ByteArray) : Writes (Writer.bytes b) b := fun s => rfl

theorem u8 (v : UInt8) : Writes (Writer.u8 v) ⟨#[v]⟩ := fun s => by
  rw [Writer.u8_eq]
  congr 2
  apply ByteArray.ext
  simp [ByteArray.data_append, ByteArray.data_push]

theorem uN {n v : Nat} (hv : v < 256 ^ n) : Writes (Writer.uN n v) (beBytes n v) :=
  fun s => Writer.uN_eq n v s hv

theorem prefixed {n : Nat} {w : Writer Unit} {o : ByteArray} (h : Writes w o)
    (hs : o.size < 256 ^ n) : Writes (Writer.prefixed n w) (beBytes n o.size ++ o) := fun s => by
  have hw : StateT.run w ByteArray.empty = .ok ((), o) := by
    simpa [StateT.run, ByteArray.empty_append] using h ByteArray.empty
  unfold Writer.prefixed
  rw [hw]
  simp only [Writer.bind_eq, Writer.pure_eq, Writer.uN_eq n o.size s hs, Writer.bytes_eq,
    ByteArray.append_assoc]

theorem foldl_append {γ : Type} (out : γ → ByteArray) :
    ∀ (l : List γ) (a b : ByteArray),
      l.foldl (fun acc x => acc ++ out x) (a ++ b) = a ++ l.foldl (fun acc x => acc ++ out x) b
  | [], _, _ => rfl
  | x :: xs, a, b => by
    simp only [List.foldl_cons, ByteArray.append_assoc]
    exact foldl_append out xs a (b ++ out x)

/-- What a `for` loop of writers writes. -/
def concatMap {γ : Type} (l : List γ) (out : γ → ByteArray) : ByteArray :=
  l.foldl (fun acc x => acc ++ out x) ByteArray.empty

theorem concatMap_cons {γ : Type} (x : γ) (xs : List γ) (out : γ → ByteArray) :
    concatMap (x :: xs) out = out x ++ concatMap xs out := by
  simp only [concatMap, List.foldl_cons, ByteArray.empty_append]
  rw [← foldl_append out xs (out x) ByteArray.empty, ByteArray.append_empty]

/-- A loop body that writes `out` and goes on. -/
def Yields (g : Writer (ForInStep PUnit)) (out : ByteArray) : Prop :=
  ∀ s, g s = .ok (.yield PUnit.unit, s ++ out)

theorem Yields.last {w : Writer Unit} {o : ByteArray} (h : Writes w o) :
    Yields (w >>= fun _ => Pure.pure (ForInStep.yield PUnit.unit)) o := fun s => by
  rw [Writer.bind_eq, h s]
  rfl

theorem Yields.bind {w : Writer Unit} {g : Writer (ForInStep PUnit)} {o o' : ByteArray}
    (h : Writes w o) (h' : Yields g o') : Yields (w >>= fun _ => g) (o ++ o') := fun s => by
  rw [Writer.bind_eq, h s]
  simp only
  rw [h' (s ++ o), ByteArray.append_assoc]

theorem forIn {γ : Type} (l : List γ) (g : γ → PUnit → Writer (ForInStep PUnit))
    (out : γ → ByteArray) (h : ∀ x ∈ l, Yields (g x PUnit.unit) (out x)) :
    Writes (ForIn.forIn l PUnit.unit g) (concatMap l out) := by
  induction l with
  | nil => intro s; simp [concatMap, ByteArray.append_empty]; rfl
  | cons x xs ih =>
    intro s
    simp only [List.forIn_cons, Writer.bind_eq, h x (by simp) s]
    rw [ih (fun y hy => h y (by simp [hy])) (s ++ out x), concatMap_cons, ByteArray.append_assoc]

end Writes

/-! ## Parsers -/

theorem _root_.ByteArray.get!_eq_getElem (B : ByteArray) (i : Nat) (h : i < B.size) :
    B.get! i = B[i] := by
  rcases B with ⟨bs⟩
  simp only [ByteArray.get!]
  exact getElem!_pos bs i h

def Reads (p : Parser α) (x : α) (out : ByteArray) : Prop :=
  ∀ (B : ByteArray) (c : Cursor), c.limit ≤ B.size → c.pos + out.size ≤ c.limit →
    B.extract c.pos (c.pos + out.size) = out → p B c = .ok (x, { c with pos := c.pos + out.size })

def ReadsAll (p : Parser α) (x : α) (out : ByteArray) : Prop :=
  ∀ (B : ByteArray) (c : Cursor), c.limit ≤ B.size → c.pos + out.size = c.limit →
    B.extract c.pos (c.pos + out.size) = out → p B c = .ok (x, { c with pos := c.pos + out.size })

namespace Reads

theorem all {p : Parser α} {x : α} {o : ByteArray} (h : Reads p x o) : ReadsAll p x o :=
  fun B c hl he hx => h B c hl (by omega) hx

theorem pure (x : α) : Reads (Pure.pure x : Parser α) x ByteArray.empty := fun B c _ _ _ => by
  simp [Parser.pure_eq]

private theorem extract_left {B o o' : ByteArray} {pos : Nat}
    (h : B.extract pos (pos + (o ++ o').size) = o ++ o') :
    B.extract pos (pos + o.size) = o := by
  have := congrArg (fun b => b.extract 0 o.size) h
  simp only [ByteArray.extract_extract, ByteArray.size_append] at this
  rw [ByteArray.extract_append_eq_left rfl] at this
  rwa [Nat.add_zero, Nat.min_eq_left (by omega)] at this

private theorem extract_right {B o o' : ByteArray} {pos : Nat}
    (h : B.extract pos (pos + (o ++ o').size) = o ++ o') :
    B.extract (pos + o.size) (pos + o.size + o'.size) = o' := by
  have := congrArg (fun b => b.extract o.size (o.size + o'.size)) h
  simp only [ByteArray.extract_extract, ByteArray.size_append] at this
  rw [ByteArray.extract_append_eq_right rfl rfl] at this
  rwa [Nat.min_eq_left (by omega), ← Nat.add_assoc] at this

theorem bind {p : Parser α} {q : α → Parser β} {x : α} {y : β} {o o' : ByteArray}
    (h : Reads p x o) (h' : Reads (q x) y o') : Reads (p >>= q) y (o ++ o') :=
  fun B c hl hle hx => by
    simp only [ByteArray.size_append] at hle
    rw [Parser.bind_eq, h B c hl (by omega) (extract_left hx)]
    have := h' B { c with pos := c.pos + o.size } hl (by simp; omega)
      (by simpa using extract_right hx)
    simpa [ByteArray.size_append, Nat.add_assoc] using this

theorem bindAll {p : Parser α} {q : α → Parser β} {x : α} {y : β} {o o' : ByteArray}
    (h : Reads p x o) (h' : ReadsAll (q x) y o') : ReadsAll (p >>= q) y (o ++ o') :=
  fun B c hl he hx => by
    simp only [ByteArray.size_append] at he
    rw [Parser.bind_eq, h B c hl (by omega) (extract_left hx)]
    have := h' B { c with pos := c.pos + o.size } hl (by simp; omega)
      (by simpa using extract_right hx)
    simpa [ByteArray.size_append, Nat.add_assoc] using this

theorem bytes {o : ByteArray} {n : Nat} (hn : o.size = n) : Reads (Parser.bytes n) o o :=
  fun B c _ hle hx => by
    subst hn
    simp [Parser.bytes_eq, hle, hx]

theorem u8 (v : UInt8) : Reads Parser.u8 v ⟨#[v]⟩ := fun B c hl hle hx => by
  have hs : (⟨#[v]⟩ : ByteArray).size = 1 := rfl
  rw [hs] at hle hx ⊢
  rw [ByteArray.extract_add_one (by omega)] at hx
  have hv : B[c.pos]'(by omega) = v := by
    have := congrArg (fun b : ByteArray => b.data) hx
    simpa using this
  simp [Parser.u8_eq, show c.pos < c.limit by omega, B.get!_eq_getElem c.pos (by omega), hv]

theorem uN {n v : Nat} (hv : v < 256 ^ n) : Reads (Parser.uN n) v (beBytes n v) := by
  have := bind (q := fun b => (Pure.pure (decodeBE b) : Parser Nat)) (bytes (size_beBytes n v))
    (pure (decodeBE (beBytes n v)))
  rw [ByteArray.append_empty, decodeBE_beBytes, Nat.mod_eq_of_lt hv] at this
  exact this

/-- The rest of the input, up to the limit. -/
theorem rest (o : ByteArray) : ReadsAll (do Parser.bytes (← Parser.remaining)) o o :=
  fun B c hl he hx => by
    simp [Parser.bind_eq, Parser.remaining_eq, Parser.bytes_eq, show c.limit - c.pos = o.size by omega,
      show c.pos + o.size ≤ c.limit by omega, hx]

theorem sub {p : Parser α} {x : α} {o : ByteArray} {n : Nat} (h : ReadsAll p x o)
    (hn : o.size = n) : Reads (Parser.sub n p) x o := fun B c hl hle hx => by
  subst hn
  have r := h B { c with limit := c.pos + o.size } (by simp; omega) (by simp) hx
  simp [Parser.sub_eq, hle, r]

theorem vec {k : Nat} {p : Parser α} {x : α} {o : ByteArray} (h : ReadsAll p x o)
    (hs : o.size < 256 ^ k) :
    Reads (do Parser.sub (← Parser.uN k) p) x (beBytes k o.size ++ o) :=
  bind (uN hs) (sub h rfl)

theorem vec8 {p : Parser α} {x : α} {o : ByteArray} (h : ReadsAll p x o) (hs : o.size < 256) :
    Reads (Parser.vec8 p) x (beBytes 1 o.size ++ o) := vec h hs

theorem vec16 {p : Parser α} {x : α} {o : ByteArray} (h : ReadsAll p x o) (hs : o.size < 256 ^ 2) :
    Reads (Parser.vec16 p) x (beBytes 2 o.size ++ o) := vec h hs

theorem vec24 {p : Parser α} {x : α} {o : ByteArray} (h : ReadsAll p x o) (hs : o.size < 256 ^ 3) :
    Reads (Parser.vec24 p) x (beBytes 3 o.size ++ o) := vec h hs

theorem opaque8 {o : ByteArray} (hs : o.size < 256) :
    Reads Parser.opaque8 o (beBytes 1 o.size ++ o) := vec8 (rest o) hs

theorem opaque16 {o : ByteArray} (hs : o.size < 256 ^ 2) :
    Reads Parser.opaque16 o (beBytes 2 o.size ++ o) := vec16 (rest o) hs

theorem opaque24 {o : ByteArray} (hs : o.size < 256 ^ 3) :
    Reads Parser.opaque24 o (beBytes 3 o.size ++ o) := vec24 (rest o) hs

theorem many_go {p : Parser α} {out : α → ByteArray} :
    ∀ (xs : List α) (fuel : Nat) (acc : Array α),
      (∀ x ∈ xs, Reads p x (out x) ∧ 0 < (out x).size) → (Writes.concatMap xs out).size ≤ fuel →
      ReadsAll (Parser.many.go p fuel acc) (acc ++ xs.toArray) (Writes.concatMap xs out)
  | [], fuel, acc, _, _ => fun B c _ he _ => by
    have hs : (Writes.concatMap ([] : List α) out).size = 0 := rfl
    rw [hs] at he ⊢
    cases fuel <;>
      simp [Parser.many.go, Parser.bind_eq, Parser.atEnd_eq, Parser.pure_eq,
        show c.limit - c.pos = 0 by omega]
  | x :: xs, fuel, acc, h, hf => fun B c hl he hx => by
    obtain ⟨hp, hpos⟩ := h x (by simp)
    rw [Writes.concatMap_cons] at hx he hf ⊢
    simp only [ByteArray.size_append] at he hf
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by omega⟩
    have r1 := hp B c hl (by omega) (extract_left hx)
    have r2 := many_go xs n (acc.push x) (fun y hy => h y (by simp [hy])) (by omega)
      B { c with pos := c.pos + (out x).size } hl (by simp; omega) (by simpa using extract_right hx)
    simp only [Parser.many.go, Parser.bind_eq, Parser.atEnd_eq, Parser.get_eq, r1, Parser.ite_eq,
      Parser.fail_eq, Parser.pure_eq, show (c.limit - c.pos == 0) = false by rw [beq_eq_false_iff_ne]; omega,
      show (c.pos + (out x).size == c.pos) = false by rw [beq_eq_false_iff_ne]; omega, r2]
    simp [ByteArray.size_append, Nat.add_assoc]

theorem many {p : Parser α} {out : α → ByteArray} (xs : List α)
    (h : ∀ x ∈ xs, Reads p x (out x) ∧ 0 < (out x).size) :
    ReadsAll (Parser.many p) xs.toArray (Writes.concatMap xs out) := fun B c hl he hx => by
  have := many_go xs (c.limit - c.pos) #[] h (by omega) B c hl he hx
  simp only [Parser.many, Parser.bind_eq, Parser.remaining_eq]
  simpa using this

end Reads

theorem Parser.run_of_readsAll {p : Parser α} {x : α} {b : ByteArray} (h : ReadsAll p x b) :
    Parser.run p b = .ok x := by
  have r := h b ⟨0, b.size⟩ (by simp) (by simp) (by simp [ByteArray.extract_zero_size])
  simp only [Nat.zero_add] at r
  show Except.bind ((p b).run ⟨0, b.size⟩) _ = _
  simp [StateT.run, r, Except.bind, pure, Except.pure]

end LeanTLS.Wire

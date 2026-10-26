/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import LeanTLS.WireLaws
import LeanTLS.Messages

namespace LeanTLS.Wire

/-! # Round trips

`RT w p x n`: the writer `w` writes at most `n` bytes, from which the parser `p` reads back `x`.
`RTAll` is the same for a parser reading up to the limit. They compose like the do-blocks they
describe, with the size bound added up, so a message's round trip follows its definition. -/

variable {α β : Type}

def RT (w : Writer Unit) (p : Parser α) (x : α) (n : Nat) : Prop :=
  ∃ out, out.size ≤ n ∧ Writes w out ∧ Reads p x out

def RTAll (w : Writer Unit) (p : Parser α) (x : α) (n : Nat) : Prop :=
  ∃ out, out.size ≤ n ∧ Writes w out ∧ ReadsAll p x out

namespace RT

theorem all {w : Writer Unit} {p : Parser α} {x : α} {n : Nat} (h : RT w p x n) : RTAll w p x n :=
  let ⟨o, hs, hw, hr⟩ := h; ⟨o, hs, hw, hr.all⟩

theorem mono {w : Writer Unit} {p : Parser α} {x : α} {n m : Nat} (h : RT w p x n) (hm : n ≤ m) :
    RT w p x m :=
  let ⟨o, hs, hw, hr⟩ := h; ⟨o, by omega, hw, hr⟩

theorem pure (x : α) : RT (Pure.pure ()) (Pure.pure x) x 0 :=
  ⟨ByteArray.empty, by simp, Writes.pure, Reads.pure x⟩

theorem bind {w v : Writer Unit} {p : Parser α} {q : α → Parser β} {x : α} {y : β} {n m : Nat}
    (h : RT w p x n) (h' : RT v (q x) y m) : RT (w >>= fun _ => v) (p >>= q) y (n + m) :=
  let ⟨o, hs, hw, hr⟩ := h
  let ⟨o', hs', hw', hr'⟩ := h'
  ⟨o ++ o', by simp; omega, hw.bind hw', hr.bind hr'⟩

theorem bindAll {w v : Writer Unit} {p : Parser α} {q : α → Parser β} {x : α} {y : β} {n m : Nat}
    (h : RT w p x n) (h' : RTAll v (q x) y m) : RTAll (w >>= fun _ => v) (p >>= q) y (n + m) :=
  let ⟨o, hs, hw, hr⟩ := h
  let ⟨o', hs', hw', hr'⟩ := h'
  ⟨o ++ o', by simp; omega, hw.bind hw', hr.bindAll hr'⟩

theorem uN {k v : Nat} (hv : v < 256 ^ k) : RT (Writer.uN k v) (Parser.uN k) v k :=
  ⟨beBytes k v, by simp, Writes.uN hv, Reads.uN hv⟩

theorem u16 {v : Nat} (hv : v < 65536) : RT (Writer.u16 v) Parser.u16 v 2 := uN hv

theorem u8 (v : UInt8) : RT (Writer.u8 v) Parser.u8 v 1 :=
  ⟨⟨#[v]⟩, Nat.le_refl 1, Writes.u8 v, Reads.u8 v⟩

theorem bytes {b : ByteArray} {n : Nat} (hn : b.size = n) : RT (Writer.bytes b) (Parser.bytes n) b n :=
  ⟨b, by omega, Writes.bytes b, Reads.bytes hn⟩

theorem vec {k : Nat} {w : Writer Unit} {p : Parser α} {x : α} {n : Nat} (h : RTAll w p x n)
    (hn : n < 256 ^ k) : RT (Writer.prefixed k w) (do Parser.sub (← Parser.uN k) p) x (k + n) :=
  let ⟨o, hs, hw, hr⟩ := h
  ⟨beBytes k o.size ++ o, by simp; omega, hw.prefixed (by omega), Reads.vec hr (by omega)⟩

theorem vec8 {w : Writer Unit} {p : Parser α} {x : α} {n : Nat} (h : RTAll w p x n)
    (hn : n < 256) : RT (Writer.prefixed 1 w) (Parser.vec8 p) x (1 + n) := vec h hn

theorem vec16 {w : Writer Unit} {p : Parser α} {x : α} {n : Nat} (h : RTAll w p x n)
    (hn : n < 65536) : RT (Writer.prefixed 2 w) (Parser.vec16 p) x (2 + n) := vec h hn

theorem vec24 {w : Writer Unit} {p : Parser α} {x : α} {n : Nat} (h : RTAll w p x n)
    (hn : n < 16777216) : RT (Writer.prefixed 3 w) (Parser.vec24 p) x (3 + n) := vec h hn

theorem opaque8 {b : ByteArray} (hn : b.size < 256) : RT (Writer.opaque8 b) Parser.opaque8 b (1 + b.size) :=
  vec8 ⟨b, Nat.le_refl _, Writes.bytes b, Reads.rest b⟩ hn

theorem opaque16 {b : ByteArray} (hn : b.size < 65536) :
    RT (Writer.opaque16 b) Parser.opaque16 b (2 + b.size) :=
  vec16 ⟨b, Nat.le_refl _, Writes.bytes b, Reads.rest b⟩ hn

theorem opaque24 {b : ByteArray} (hn : b.size < 16777216) :
    RT (Writer.opaque24 b) Parser.opaque24 b (3 + b.size) :=
  vec24 ⟨b, Nat.le_refl _, Writes.bytes b, Reads.rest b⟩ hn

/-- Items written by a loop and read by `many`, each in at least one byte and at most `bound x`. -/
theorem many {γ : Type} {g : γ → PUnit → Writer (ForInStep PUnit)} {p : Parser γ}
    (bound : γ → Nat) (xs : List γ)
    (h : ∀ x ∈ xs, ∃ out, 0 < out.size ∧ out.size ≤ bound x ∧ Writes.Yields (g x PUnit.unit) out ∧
      Reads p x out) :
    RTAll (ForIn.forIn xs PUnit.unit g) (Parser.many p) xs.toArray (xs.map bound).sum := by
  classical
  let out : γ → ByteArray := fun x => if hx : x ∈ xs then Classical.choose (h x hx) else ByteArray.empty
  have spec : ∀ x ∈ xs, 0 < (out x).size ∧ (out x).size ≤ bound x ∧
      Writes.Yields (g x PUnit.unit) (out x) ∧ Reads p x (out x) :=
    fun x hx => by simp only [out, dite_eq_left hx]; exact Classical.choose_spec (h x hx)
  refine ⟨Writes.concatMap xs out, ?_, Writes.forIn xs g out fun x hx => (spec x hx).2.2.1,
    Reads.many xs fun x hx => ⟨(spec x hx).2.2.2, (spec x hx).1⟩⟩
  clear_value out
  induction xs with
  | nil => simp [Writes.concatMap]
  | cons x xs ih =>
    rw [Writes.concatMap_cons, ByteArray.size_append, List.map_cons, List.sum_cons]
    have := (spec x (by simp)).2.1
    have := ih (fun y hy => h y (by simp [hy])) (fun y hy => spec y (by simp [hy]))
    omega

/-- One item read by `many`. -/
theorem many1 {w : Writer Unit} {p : Parser α} {x : α} {n : Nat} (h : RT w p x n)
    (hne : ∀ out, Writes w out → 0 < out.size) : RTAll w (Parser.many p) #[x] n := by
  obtain ⟨o, hs, hw, hr⟩ := h
  refine ⟨o, hs, hw, ?_⟩
  have := Reads.many (out := fun _ => o) [x] (by simpa using ⟨hr, hne o hw⟩)
  simpa [Writes.concatMap, ByteArray.empty_append] using this

/-- The parser goes on to `q`, reading nothing more. -/
theorem tail {w : Writer Unit} {p : Parser α} {q : α → Parser β} {x : α} {y : β} {n : Nat}
    (h : RT w p x n) (hq : Reads (q x) y ByteArray.empty) : RT w (p >>= q) y n :=
  let ⟨o, hs, hw, hr⟩ := h
  ⟨o, hs, hw, by simpa [ByteArray.append_empty] using hr.bind hq⟩

theorem tailAll {w : Writer Unit} {p : Parser α} {q : α → Parser β} {x : α} {y : β} {n : Nat}
    (h : RTAll w p x n) (hq : Reads (q x) y ByteArray.empty) : RTAll w (p >>= q) y n :=
  let ⟨o, hs, hw, hr⟩ := h
  ⟨o, hs, hw, fun B c hl he hx => by
    rw [Parser.bind_eq, hr B c hl he hx]
    have := hq B { c with pos := c.pos + o.size } hl (by simp; omega) (by simp)
    simpa using this⟩

/-- A check the parser makes, which the writer's output passes. -/
theorem guard {w : Writer Unit} {p : Parser α} {x : α} {n : Nat} {c : Prop} [Decidable c]
    {e : Parser PUnit} (hc : ¬c) (h : RT w p x n) :
    RT w ((if c then e else Pure.pure PUnit.unit) >>= fun _ => p) x n := by
  rw [ite_eq_right_iff.mpr (fun h => absurd h hc)]
  obtain ⟨o, hs, hw, hr⟩ := h
  exact ⟨o, hs, hw, by
    simpa [ByteArray.empty_append] using (Reads.pure PUnit.unit).bind (q := fun _ => p) hr⟩

theorem guardAll {w : Writer Unit} {p : Parser α} {x : α} {n : Nat} {c : Prop} [Decidable c]
    {e : Parser PUnit} (hc : ¬c) (h : RTAll w p x n) :
    RTAll w ((if c then e else Pure.pure PUnit.unit) >>= fun _ => p) x n := by
  rw [ite_eq_right_iff.mpr (fun h => absurd h hc)]
  obtain ⟨o, hs, hw, hr⟩ := h
  exact ⟨o, hs, hw, by
    simpa [ByteArray.empty_append] using (Reads.pure PUnit.unit).bindAll (q := fun _ => p) hr⟩

theorem pureW {w : Writer PUnit} {p : Parser α} {x : α} {n : Nat} (h : RTAll w p x n) :
    RTAll (w >>= fun (_ : PUnit) => (Pure.pure () : Writer Unit)) p x n :=
  let ⟨o, hs, hw, hr⟩ := h
  ⟨o, hs, by simpa [ByteArray.append_empty] using hw.bind Writes.pure, hr⟩

theorem run {w : Writer Unit} {p : Parser α} {x : α} {n : Nat} (h : RTAll w p x n) :
    ∃ b, Writer.run w = .ok b ∧ Parser.run p b = .ok x ∧ b.size ≤ n :=
  let ⟨o, hs, hw, hr⟩ := h
  ⟨o, hw.run, Parser.run_of_readsAll hr, hs⟩

end RT

end LeanTLS.Wire

namespace LeanTLS.Messages

open LeanTLS.Wire

/-! ## Extensions -/

def Extension.WF (e : Extension) : Prop := e.typ < 65536 ∧ e.data.size < 65536

theorem rt_extension {e : Extension} (h : e.WF) :
    RT (writeExtension e) extension e (4 + e.data.size) := by
  rcases e with ⟨typ, data⟩
  have : RT (writeExtension ⟨typ, data⟩) extension ⟨typ, data⟩ (2 + (2 + data.size)) := by
    unfold writeExtension extension
    exact RT.bind (RT.u16 h.1) (RT.tail (RT.opaque16 h.2) (Reads.pure _))
  exact this.mono (by simp; omega)

theorem writes_extension_pos {e : Extension} (h : e.WF) {o : ByteArray}
    (hw : Writes (writeExtension e) o) : 0 < o.size := by
  obtain ⟨o', -, hw', -⟩ := RT.opaque16 h.2
  have := hw.det ((Writes.uN h.1).bind hw')
  subst this
  simp only [ByteArray.size_append, size_beBytes]
  omega

/-- Bytes the extensions take behind their 2-byte length. -/
def extsSize (exts : Array Extension) : Nat := (exts.toList.map fun e => 4 + e.data.size).sum

def ExtsWF (exts : Array Extension) : Prop :=
  (∀ e ∈ exts.toList, e.WF) ∧ dupTypes exts.toList = false ∧ extsSize exts < 65536

theorem rt_extensions {exts : Array Extension} (h : ExtsWF exts) :
    RT (writeExtensions exts) extensions exts (2 + extsSize exts) := by
  obtain ⟨hwf, hdup, hsize⟩ := h
  unfold writeExtensions extensions
  rw [← Array.forIn_toList]
  have hm := RT.many (p := extension)
    (g := fun e _ => do writeExtension e; pure (ForInStep.yield PUnit.unit)) (fun e => 4 + e.data.size) exts.toList
    fun e he => let ⟨o, hs, hw, hr⟩ := rt_extension (hwf e he)
      ⟨o, writes_extension_pos (hwf e he) hw, hs, Writes.Yields.last hw, hr⟩
  simp only [Array.toArray_toList] at hm
  refine RT.tail (RT.vec16 (RT.pureW hm) hsize) ?_
  simp only [hdup, Bool.false_eq_true, ↓reduceIte]
  exact Reads.pure exts

theorem sum_const {γ : Type} (k : Nat) : ∀ xs : List γ, (xs.map fun _ => k).sum = k * xs.length
  | [] => rfl
  | _ :: xs => by simp only [List.map_cons, List.sum_cons, List.length_cons, sum_const k xs, Nat.mul_succ]; omega

theorem rt_u16List (xs : List Nat) (h : ∀ x ∈ xs, x < 65536) :
    RTAll (ForIn.forIn xs PUnit.unit fun x _ => do Writer.u16 x; Pure.pure (ForInStep.yield PUnit.unit))
      u16List xs.toArray (2 * xs.length) := by
  have := RT.many (p := Parser.u16)
    (g := fun x _ => do Writer.u16 x; pure (ForInStep.yield PUnit.unit)) (fun _ => 2) xs fun x hx =>
    ⟨beBytes 2 x, by simp, by simp, Writes.Yields.last (Writes.uN (h x hx)), Reads.uN (h x hx)⟩
  rw [sum_const] at this
  exact this

structure ClientHello.WF (m : ClientHello) : Prop where
  random : m.random.size = 32
  sessionId : m.sessionId.size ≤ 32
  suites : ∀ s ∈ m.cipherSuites.toList, s < 65536
  suitesSize : 2 * m.cipherSuites.size < 65536
  exts : ExtsWF m.extensions

def ClientHello.size (m : ClientHello) : Nat :=
  2 + 32 + (1 + m.sessionId.size) + (2 + 2 * m.cipherSuites.size) + 2 + (2 + extsSize m.extensions)

theorem rt_clientHello {m : ClientHello} (h : m.WF) :
    RT (writeClientHello m) clientHello m m.size := by
  rcases m with ⟨random, sessionId, suites, exts⟩
  unfold writeClientHello clientHello
  apply RT.mono
  · apply RT.bind (RT.u16 (v := legacyVersion) (by decide))
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    apply RT.bind (RT.bytes h.random)
    apply RT.bind (RT.opaque8 (by have := h.sessionId; simp at this ⊢; omega))
    simp only [show ¬ sessionId.size > 32 from Nat.not_lt.mpr h.sessionId, ↓reduceIte]
    rw [← Array.forIn_toList]
    have hs := rt_u16List suites.toList h.suites
    simp only [Array.toArray_toList, Array.length_toList] at hs
    apply RT.bind (RT.vec16 (RT.pureW hs) h.suitesSize)
    apply RT.bind (RT.opaque8 (b := ⟨#[0]⟩) (by decide))
    simp only [show ((⟨#[0]⟩ : ByteArray).data != #[0]) = false by decide, Bool.false_eq_true,
      ↓reduceIte]
    exact RT.tail (rt_extensions h.exts) (Reads.pure _)
  · simp only [ClientHello.size]
    have : (⟨#[0]⟩ : ByteArray).size = 1 := rfl
    omega

structure ServerHello.WF (m : ServerHello) : Prop where
  random : m.random.size = 32
  sessionId : m.sessionId.size ≤ 32
  suite : m.cipherSuite < 65536
  exts : ExtsWF m.extensions

def ServerHello.size (m : ServerHello) : Nat :=
  2 + 32 + (1 + m.sessionId.size) + 2 + 1 + (2 + extsSize m.extensions)

theorem rt_serverHello {m : ServerHello} (h : m.WF) :
    RT (writeServerHello m) serverHello m m.size := by
  rcases m with ⟨random, sessionId, suite, exts⟩
  unfold writeServerHello serverHello
  apply RT.mono
  · apply RT.bind (RT.u16 (v := legacyVersion) (by decide))
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    apply RT.bind (RT.bytes h.random)
    apply RT.bind (RT.opaque8 (by have := h.sessionId; simp at this ⊢; omega))
    simp only [show ¬ sessionId.size > 32 from Nat.not_lt.mpr h.sessionId, ↓reduceIte]
    apply RT.bind (RT.u16 h.suite)
    apply RT.bind (RT.u8 0)
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    exact RT.tail (rt_extensions h.exts) (Reads.pure _)
  · simp only [ServerHello.size]
    omega

theorem rt_keyShareEntry {e : KeyShareEntry} (hg : e.group < 65536) (hk : e.key.size < 65536) :
    RT (writeKeyShareEntry e) keyShareEntry e (4 + e.key.size) := by
  rcases e with ⟨group, key⟩
  unfold writeKeyShareEntry keyShareEntry
  apply RT.mono
  · exact RT.bind (RT.u16 hg) (RT.tail (RT.opaque16 hk) (Reads.pure _))
  · simp only; omega

theorem rt_certificateVerify {m : CertificateVerify} (hs : m.scheme < 65536)
    (hk : m.signature.size < 65536) :
    RT (writeCertificateVerify m) certificateVerify m (4 + m.signature.size) := by
  rcases m with ⟨scheme, signature⟩
  unfold writeCertificateVerify certificateVerify
  apply RT.mono
  · exact RT.bind (RT.u16 hs) (RT.tail (RT.opaque16 hk) (Reads.pure _))
  · simp only; omega

/-- A certificate message with one entry. -/
theorem rt_certificate {data : ByteArray} (hd : data.size < 65536) :
    RT (writeCertificate ⟨ByteArray.empty, #[⟨data, ByteArray.empty⟩]⟩) certificate
      ⟨ByteArray.empty, #[⟨data, ByteArray.empty⟩]⟩ (9 + data.size) := by
  unfold writeCertificate certificate
  have he : RT (do Writer.opaque24 data; Writer.opaque16 ByteArray.empty)
      (do let data ← Parser.opaque24; let extensions ← Parser.opaque16; pure { data, extensions })
      (⟨data, ByteArray.empty⟩ : CertificateEntry) (3 + data.size + 2) := by
    apply RT.mono
    · exact RT.bind (RT.opaque24 (by omega)) (RT.tail (RT.opaque16 (by decide)) (Reads.pure _))
    · simp
  have hm := RT.many
    (p := (do let data ← Parser.opaque24; let extensions ← Parser.opaque16; pure { data, extensions } :
      Parser CertificateEntry))
    (g := fun (e : CertificateEntry) (_ : PUnit) => do
      Writer.opaque24 e.data; Writer.opaque16 e.extensions; pure (ForInStep.yield PUnit.unit))
    (fun _ => 3 + data.size + 2) [⟨data, ByteArray.empty⟩] fun e he' => by
      simp only [List.mem_singleton] at he'
      subst he'
      obtain ⟨o, hs, hw, hr⟩ := he
      obtain ⟨o1, -, hw1, -⟩ := RT.opaque24 (b := data) (by omega)
      obtain ⟨o2, -, hw2, -⟩ := RT.opaque16 (b := ByteArray.empty) (by decide)
      have := hw.det (hw1.bind hw2)
      subst this
      refine ⟨o1 ++ o2, ?_, hs, ?_, hr⟩
      · have := hw1.det ((Writes.uN (n := 3) (v := data.size) (by omega)).bind (Writes.bytes data))
        subst this
        simp only [ByteArray.size_append, size_beBytes]
        omega
      · exact Writes.Yields.bind hw1 (Writes.Yields.last hw2)
  rw [← Array.forIn_toList]
  dsimp only
  apply RT.mono
  · apply RT.bind (RT.opaque8 (b := ByteArray.empty) (by decide))
    exact RT.tail (RT.vec24 (RT.pureW hm) (by simp; omega)) (Reads.pure _)
  · simp; omega

def AlpnWF (ps : List ByteArray) : Prop := ∀ p ∈ ps, 0 < p.size ∧ p.size < 256

theorem rt_alpnList {ps : List ByteArray} (h : AlpnWF ps)
    (hs : (ps.map fun p => 1 + p.size).sum < 65536) :
    RT (writeAlpnList ps.toArray) alpnList ps.toArray (2 + (ps.map fun p => 1 + p.size).sum) := by
  unfold writeAlpnList alpnList
  rw [← Array.forIn_toList]
  have hm := RT.many (p := do let p ← Parser.opaque8; if p.size == 0 then Parser.fail else pure p)
    (g := fun p _ => do Writer.opaque8 p; pure (ForInStep.yield PUnit.unit))
    (fun p => 1 + p.size) ps fun p hp => by
      obtain ⟨o, hs, hw, hr⟩ := RT.tail (q := fun p : ByteArray => if p.size == 0 then Parser.fail else pure p)
        (RT.opaque8 (h p hp).2) (by
          simp only [show (p.size == 0) = false by rw [beq_eq_false_iff_ne]; exact Nat.ne_of_gt (h p hp).1,
            Bool.false_eq_true, ↓reduceIte]
          exact Reads.pure p)
      refine ⟨o, ?_, hs, Writes.Yields.last hw, hr⟩
      have := hw.det ((Writes.uN (n := 1) (v := p.size) (h p hp).2).bind (Writes.bytes p))
      subst this
      simp only [ByteArray.size_append, size_beBytes]
      omega
  exact RT.vec16 (RT.pureW hm) hs

/-! ## Frames -/

/-- A handshake message on the wire: type, 24-bit length, body. -/
def frameBytes (typ : UInt8) (body : ByteArray) : ByteArray :=
  ⟨#[typ]⟩ ++ (beBytes 3 body.size ++ body)

theorem size_frameBytes (typ : UInt8) (body : ByteArray) :
    (frameBytes typ body).size = 4 + body.size := by
  simp only [frameBytes, ByteArray.size_append, size_beBytes]
  have : (⟨#[typ]⟩ : ByteArray).size = 1 := rfl
  omega

theorem frame_eq {typ : UInt8} {w : Writer Unit} {o : ByteArray} (h : Writes w o)
    (hs : o.size < 256 ^ 3) : frame typ w = .ok (frameBytes typ o) :=
  ((Writes.u8 typ).bind (h.prefixed hs)).run

/-- Messages one after another. -/
def frames : List (UInt8 × ByteArray) → ByteArray
  | [] => ByteArray.empty
  | (t, b) :: rest => frameBytes t b ++ frames rest

def rawOf (m : UInt8 × ByteArray) : RawMessage := ⟨m.1, m.2, frameBytes m.1 m.2⟩

theorem extract_prefix {B X Y : ByteArray} {i : Nat} (hi : i ≤ B.size)
    (h : B.extract i B.size = X ++ Y) :
    B.extract i (i + X.size) = X ∧ B.extract (i + X.size) B.size = Y ∧ i + X.size ≤ B.size := by
  have hsize := congrArg ByteArray.size h
  simp only [ByteArray.size_extract, ByteArray.size_append, Nat.min_self] at hsize
  refine ⟨?_, ?_, by omega⟩
  · have := congrArg (fun b => b.extract 0 X.size) h
    simp only [ByteArray.extract_extract, ByteArray.extract_append_eq_left rfl] at this
    rwa [Nat.add_zero, Nat.min_eq_left (by omega)] at this
  · have := congrArg (fun b => b.extract X.size (X.size + Y.size)) h
    simp only [ByteArray.extract_extract, ByteArray.extract_append_eq_right rfl rfl] at this
    rwa [Nat.min_eq_right (by omega)] at this

theorem get!_of_extract {B X : ByteArray} {i k : Nat} (h : B.extract i (i + X.size) = X)
    (hle : i + X.size ≤ B.size) (hk : k < X.size) : B.get! (i + k) = X[k] := by
  rw [ByteArray.get!_eq_getElem B (i + k) (by omega)]
  have := congrArg (fun b : ByteArray => b[k]!) h
  rw [getElem!_pos X k hk, getElem!_pos _ k (by simp; omega), ByteArray.getElem_extract] at this
  exact this

theorem len24 (v : Nat) (hv : v < 256 ^ 3) :
    (UInt8.ofNat (v >>> 16)).toNat * 65536 + (UInt8.ofNat (v >>> 8)).toNat * 256 +
      (UInt8.ofNat v).toNat = v := by
  simp only [UInt8.toNat_ofNat', Nat.shiftRight_eq_div_pow, show (2 : Nat) ^ 16 = 65536 by rfl,
    show (2 : Nat) ^ 8 = 256 by rfl]
  omega

theorem splitMessages_go (buf : ByteArray) :
    ∀ (l : List (UInt8 × ByteArray)) (fuel pos : Nat) (acc : Array RawMessage),
      (∀ m ∈ l, m.2.size ≤ maxMessageSize) → l.length ≤ fuel → pos ≤ buf.size →
      buf.extract pos buf.size = frames l →
      splitMessages.go buf fuel pos acc = .ok (acc ++ (l.map rawOf).toArray, ByteArray.empty)
  | [], fuel, pos, acc, _, _, hp, hx => by
    have hs := congrArg ByteArray.size hx
    simp only [ByteArray.size_extract, Nat.min_self, frames, ByteArray.size_empty] at hs
    cases fuel with
    | zero => simp [splitMessages.go, hx, frames, pure, Except.pure]
    | succ n =>
      simp [splitMessages.go, show pos + 4 > buf.size by omega, hx, frames, pure, Except.pure]
  | (t, b) :: rest, fuel, pos, acc, hm, hl, hp, hx => by
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by simp at hl; omega⟩
    have hb : b.size ≤ maxMessageSize := hm (t, b) (by simp)
    have hbs : b.size < 256 ^ 3 := by unfold maxMessageSize at hb; omega
    have hx' : buf.extract pos buf.size = (⟨#[t]⟩ ++ beBytes 3 b.size) ++ (b ++ frames rest) := by
      rw [hx]; simp only [frames, frameBytes, ByteArray.append_assoc]
    have h4 : (⟨#[t]⟩ ++ beBytes 3 b.size : ByteArray).size = 4 := by
      simp only [ByteArray.size_append, size_beBytes]; rfl
    obtain ⟨hhead, hbody, hle⟩ := extract_prefix hp hx'
    rw [h4] at hhead hbody hle
    obtain ⟨hb1, hb2, hle2⟩ := extract_prefix hle hbody
    obtain ⟨hf, -, -⟩ := extract_prefix hp hx
    rw [size_frameBytes] at hf
    have hbyte : ∀ k (hk : k < 4), buf.get! (pos + k) = (frameBytes t b)[k]'(by
        rw [size_frameBytes]; omega) := fun k hk =>
      get!_of_extract (by rwa [size_frameBytes]) (by rw [size_frameBytes]; omega)
        (by rw [size_frameBytes]; omega)
    have hdata : ∀ k (hk : k < 4), (frameBytes t b)[k]'(by rw [size_frameBytes]; omega) =
        [t, UInt8.ofNat (b.size >>> 16), UInt8.ofNat (b.size >>> 8), UInt8.ofNat b.size][k] := by
      intro k hk
      match k, hk with
      | 0, _ | 1, _ | 2, _ | 3, _ =>
        simp [frameBytes, ByteArray.getElem_eq_getElem_data, ByteArray.data_append, beBytes]
    have hlen : (buf.get! (pos + 1)).toNat * 65536 + (buf.get! (pos + 2)).toNat * 256 +
        (buf.get! (pos + 3)).toNat = b.size := by
      rw [hbyte 1 (by omega), hbyte 2 (by omega), hbyte 3 (by omega), hdata 1 (by omega),
        hdata 2 (by omega), hdata 3 (by omega)]
      exact len24 b.size hbs
    have ht : buf.get! pos = t := by
      have := hbyte 0 (by omega)
      rw [hdata 0 (by omega)] at this
      simpa using this
    have ih := splitMessages_go buf rest n (pos + 4 + b.size)
      (acc.push ⟨t, b, frameBytes t b⟩) (fun m hm' => hm m (by simp [hm'])) (by simp at hl; omega)
      hle2 hb2
    simp only [splitMessages.go, hlen, ht, show ¬ pos + 4 > buf.size by omega,
      show ¬ b.size > maxMessageSize by omega, show ¬ pos + 4 + b.size > buf.size by omega,
      ↓reduceIte, hb1, show pos + (4 + b.size) = pos + 4 + b.size by omega] at hf ⊢
    rw [hf, ih]
    simp [rawOf]

theorem splitMessages_frames (l : List (UInt8 × ByteArray))
    (h : ∀ m ∈ l, m.2.size ≤ maxMessageSize) :
    splitMessages (frames l) = .ok ((l.map rawOf).toArray, ByteArray.empty) := by
  have hl : l.length ≤ (frames l).size := by
    clear h
    induction l with
    | nil => simp
    | cons m rest ih =>
      simp only [frames, ByteArray.size_append, size_frameBytes, List.length_cons]
      omega
  unfold splitMessages
  simpa using splitMessages_go (frames l) l (frames l).size 0 #[] h hl (by omega)
    (by simp [ByteArray.extract_zero_size])

end LeanTLS.Messages

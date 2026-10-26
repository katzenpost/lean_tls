/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import LeanTLS.Handshake.Client
import LeanTLS.Handshake.Server
import LeanTLS.MessageLaws
import LeanTLS.Agreement

namespace LeanTLS.Handshake

open LeanTLS.Messages
open LeanTLS.Wire
open Cryptlib.Util.Bytes (toVecN ofVector)

/-! # An honest handshake completes with matching keys

`run` plays a client and a server against each other, delivering each side's output to the other
as QUIC would: the ClientHello, then the server's flight, then the client's Finished.
`handshake_correct`: when the two configurations are compatible (the same group, a common cipher
suite and ALPN, the server's certificate pinned by the client and holding its signing key) and the
key exchange is `Reliable` and accepted, both sides end established, and each level's keys match:
what the client reads, the server writes, and the other way round. -/

/-! ## Delivering output -/

def sendsOf (outs : Array Output) : List (Level × ByteArray) :=
  outs.toList.filterMap fun | .send l d => some (l, d) | _ => none

def installsOf (outs : Array Output) : List (Level × Suite × Secrets) :=
  outs.toList.filterMap fun | .install l s k => some (l, s, k) | _ => none

def deliver {σ : Type} (recv : σ → Level → ByteArray → Except Alert (σ × Array Output)) :
    σ → List (Level × ByteArray) → Except Alert (σ × Array Output)
  | s, [] => pure (s, #[])
  | s, (l, d) :: rest => do
    let (s, o) ← recv s l d
    let (s, o') ← deliver recv s rest
    pure (s, o ++ o')

def run (cfgC : Client.Config) (cfgS : Server.Config) (seedC seedS : Vector UInt8 32) :
    Except Alert (Client.State cfgC × Array Output × Server.State × Array Output) := do
  let (c, oc0) ← Client.start cfgC seedC
  let (s, os1) ← deliver (Server.recv cfgS seedS) Server.init (sendsOf oc0)
  let (c, oc1) ← deliver Client.recv c (sendsOf os1)
  let (s, os2) ← deliver (Server.recv cfgS seedS) s (sendsOf oc1)
  pure (c, oc0 ++ oc1, s, os1 ++ os2)

/-! ## Small facts -/

theorem ext_eq {typ : Nat} {w : Writer Unit} {o : ByteArray} (h : Writes w o) :
    ext typ w = .ok ⟨typ, o⟩ := by
  simp [ext, h.run, bind, Except.bind, pure, Except.pure]

theorem require_some {α : Type} (x : α) (a : Alert) : require (some x) a = .ok x := rfl

theorem RT.reads_of {α : Type} {w : Writer Unit} {p : Parser α} {x : α} {n : Nat} {o : ByteArray}
    (h : RT w p x n) (hw : Writes w o) : Reads p x o :=
  let ⟨_, _, hw', hr⟩ := h; (hw'.det hw) ▸ hr

theorem Reads.run {α : Type} {p : Parser α} {x : α} {o : ByteArray} (h : Reads p x o) :
    Parser.run p o = .ok x :=
  Parser.run_of_readsAll h.all

theorem group_sizes (g : Group) :
    g.keyShare.clientShareSize ≤ 2048 ∧ g.keyShare.serverShareSize ≤ 2048 ∧ g.keyShare.group < 65536 := by
  cases g <;> refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ## The ClientHello's extensions -/

def u16Bytes (v : Nat) : ByteArray := beBytes 2 v

def svData : ByteArray := beBytes 1 2 ++ u16Bytes Messages.tls13
def groupsData (g : Nat) : ByteArray := beBytes 2 2 ++ u16Bytes g
/-- The signature schemes a client offers, as a `signature_algorithms` extension. -/
def sigData (schemes : List Scheme) : ByteArray :=
  beBytes 2 (2 * schemes.length) ++ Writes.concatMap (schemes.map Scheme.code) u16Bytes
def ksData (g : Nat) (share : ByteArray) : ByteArray :=
  beBytes 2 (4 + share.size) ++ (u16Bytes g ++ (beBytes 2 share.size ++ share))
def alpnData (a : ByteArray) : ByteArray := beBytes 2 (1 + a.size) ++ (beBytes 1 a.size ++ a)
def snData (n : ByteArray) : ByteArray := beBytes 2 (3 + n.size) ++ (⟨#[0]⟩ ++ (beBytes 2 n.size ++ n))

theorem writes_sv : Writes (Writer.prefixed 1 (Writer.u16 Messages.tls13)) svData := by
  have := (Writes.uN (n := 2) (v := Messages.tls13) (by decide)).prefixed (n := 1) (by simp)
  simpa [svData, u16Bytes, Writer.u16] using this

theorem writes_u16list {g : Nat} (hg : g < 65536) :
    Writes (Writer.prefixed 2 (Writer.u16 g)) (beBytes 2 2 ++ u16Bytes g) := by
  have := (Writes.uN (n := 2) (v := g) hg).prefixed (n := 2) (by simp)
  simpa [u16Bytes, Writer.u16] using this

theorem writes_ks {g : Nat} {share : ByteArray} (hg : g < 65536) (hs : share.size < 65000) :
    Writes (Writer.prefixed 2 (writeKeyShareEntry { group := g, key := share })) (ksData g share) := by
  have hw : Writes (writeKeyShareEntry { group := g, key := share })
      (u16Bytes g ++ (beBytes 2 share.size ++ share)) :=
    (Writes.uN hg).bind ((Writes.bytes share).prefixed (by omega))
  have := hw.prefixed (n := 2) (by simp [u16Bytes]; omega)
  simp only [ByteArray.size_append, u16Bytes, size_beBytes] at this
  rwa [show 2 + (2 + share.size) = 4 + share.size by omega] at this

theorem writes_alpn {a : ByteArray} (ha : a.size < 256) :
    Writes (writeAlpnList #[a]) (alpnData a) := by
  unfold writeAlpnList
  rw [← Array.forIn_toList]
  have hw : Writes (ForIn.forIn [a] PUnit.unit fun p _ => do
      Writer.opaque8 p; Pure.pure (ForInStep.yield PUnit.unit)) (beBytes 1 a.size ++ a) := by
    have := Writes.forIn [a] (fun p _ => do Writer.opaque8 p; Pure.pure (ForInStep.yield PUnit.unit))
      (fun p => beBytes 1 p.size ++ p) (by
        intro p hp
        simp only [List.mem_singleton] at hp
        subst hp
        exact Writes.Yields.last ((Writes.bytes p).prefixed ha))
    simpa [Writes.concatMap, ByteArray.empty_append] using this
  have := (Writes.bind hw Writes.pure).prefixed (n := 2) (by simp; omega)
  simpa [alpnData, ByteArray.append_empty, Nat.add_comm] using this

theorem code_lt (s : Scheme) : s.code < 65536 := by cases s <;> decide

theorem concatMap_map {γ : Type} (f : γ → Nat) (out : Nat → ByteArray) :
    ∀ l : List γ, Writes.concatMap (l.map f) out = Writes.concatMap l (out ∘ f)
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, Writes.concatMap_cons, concatMap_map f out xs, Function.comp]

theorem size_concatMap_u16 : ∀ l : List Nat, (Writes.concatMap l u16Bytes).size = 2 * l.length
  | [] => rfl
  | x :: xs => by
    simp only [Writes.concatMap_cons, ByteArray.size_append, u16Bytes, size_beBytes,
      size_concatMap_u16 xs, List.length_cons]
    omega

theorem writes_sig (schemes : List Scheme) (h : schemes.length ≤ 100) :
    Writes (Writer.prefixed 2 (for s in schemes do Writer.u16 s.code)) (sigData schemes) := by
  have hf := Writes.forIn schemes (fun s _ => do Writer.u16 s.code; Pure.pure (ForInStep.yield PUnit.unit))
    (fun s => u16Bytes s.code) (fun s _ => Writes.Yields.last (Writes.uN (code_lt s)))
  have hsz : (Writes.concatMap schemes fun s => u16Bytes s.code).size = 2 * schemes.length := by
    have := size_concatMap_u16 (schemes.map Scheme.code)
    rw [concatMap_map, List.length_map] at this
    exact this
  have := (hf.bind Writes.pure).prefixed (n := 2) (by rw [ByteArray.append_empty, hsz]; omega)
  rw [ByteArray.append_empty, hsz] at this
  unfold sigData
  rw [concatMap_map]
  exact this

theorem decode_sig (schemes : List Scheme) (h : schemes.length ≤ 100) :
    decodeExt (Parser.vec16 u16List) (sigData schemes) = .ok (schemes.map Scheme.code).toArray := by
  have hm := Reads.many (p := Parser.u16) (out := u16Bytes) (schemes.map Scheme.code) (by
    intro x hx
    obtain ⟨s, -, rfl⟩ := List.mem_map.mp hx
    exact ⟨Reads.uN (code_lt s), by simp [u16Bytes]⟩)
  have := Reads.vec16 hm (by rw [size_concatMap_u16]; simp; omega)
  rw [size_concatMap_u16, List.length_map] at this
  exact Reads.run this

/-- What the client's configuration must satisfy for its messages to be well formed. -/
structure ClientOK (cfg : Client.Config) : Prop where
  alpnPos : 0 < cfg.alpn.size
  alpnSize : cfg.alpn.size < 256
  tps : cfg.transportParams.size ≤ 16384
  name : ∀ n, cfg.serverName = some n → n.toUTF8.size ≤ 255
  suites : cfg.suites.length ≤ 64
  schemes : cfg.schemes.length ≤ 100

def chTail (cfg : Client.Config) (share : ByteArray) : Array Extension :=
  #[⟨ExtType.supportedVersions, svData⟩, ⟨ExtType.supportedGroups, groupsData cfg.share.group⟩,
    ⟨ExtType.signatureAlgorithms, sigData cfg.schemes⟩, ⟨ExtType.keyShare, ksData cfg.share.group share⟩,
    ⟨ExtType.alpn, alpnData cfg.alpn⟩, ⟨ExtType.quicTransportParameters, cfg.transportParams⟩]

def chExts (cfg : Client.Config) (share : ByteArray) : Array Extension :=
  match cfg.serverName with
  | some name => #[⟨ExtType.serverName, snData name.toUTF8⟩] ++ chTail cfg share
  | none => chTail cfg share

theorem writes_sn {n : ByteArray} (hn : n.size ≤ 255) :
    Writes (Writer.prefixed 2 do Writer.u8 0; Writer.opaque16 n) (snData n) := by
  have h1 : (⟨#[0]⟩ : ByteArray).size = 1 := rfl
  have := ((Writes.u8 0).bind ((Writes.bytes n).prefixed (n := 2) (by omega))).prefixed (n := 2)
    (by simp only [ByteArray.size_append, size_beBytes, h1]; omega)
  simp only [ByteArray.size_append, size_beBytes] at this
  rw [show (⟨#[0]⟩ : ByteArray).size = 1 from rfl, show 1 + (2 + n.size) = 3 + n.size by omega] at this
  exact this

theorem clientHello_eq (cfg : Client.Config) (h : ClientOK cfg) (random share : ByteArray)
    (hs : share.size ≤ 2048) :
    Client.clientHello cfg random share = frame HandshakeType.clientHello (writeClientHello
      { random, sessionId := ByteArray.empty, cipherSuites := (cfg.suites.map (·.id)).toArray,
        extensions := chExts cfg share }) := by
  have hg : cfg.share.group < 65536 := (group_sizes cfg.group).2.2
  unfold Client.clientHello
  rw [ext_eq writes_sv, ext_eq (writes_u16list hg), ext_eq (writes_sig cfg.schemes h.schemes),
    ext_eq (writes_ks (share := share) hg (by omega)), ext_eq (writes_alpn h.alpnSize)]
  rcases hn : cfg.serverName with _ | name
  · simp [chExts, chTail, hn, groupsData, sigData, bind, Except.bind]
  · simp only [ext_eq (writes_sn (h.name name hn))]
    simp [chExts, chTail, hn, groupsData, sigData, bind, Except.bind]

theorem draw_size (seed : Vector UInt8 32) (label : String) (n : Nat) : (draw seed label n).size = n :=
  Cryptlib.Primitives.KDF.HKDF.expand_size _ _ _ n

theorem suite_id_lt (s : Suite) : s.id < 65536 := by cases s <;> decide

theorem suite_id_inj {s t : Suite} (h : s.id = t.id) : s = t := by
  cases s <;> cases t <;> first | rfl | exact absurd h (by decide)

theorem sig_size (cfg : Client.Config) (h : ClientOK cfg) :
    (Writes.concatMap (List.map Scheme.code cfg.schemes) u16Bytes).size ≤ 200 := by
  rw [size_concatMap_u16, List.length_map]
  have := h.schemes
  omega

theorem chExts_size (cfg : Client.Config) (h : ClientOK cfg) (share : ByteArray)
    (hs : share.size ≤ 2048) : extsSize (chExts cfg share) ≤ 20000 := by
  have hsg := sig_size cfg h
  have tp := h.tps
  have al := h.alpnSize
  have h1 : (⟨#[0]⟩ : ByteArray).size = 1 := rfl
  unfold chExts chTail
  rcases hn : cfg.serverName with _ | name
  · simp [extsSize, svData, groupsData, sigData, ksData, alpnData, u16Bytes]; omega
  · have hname : name.utf8ByteSize ≤ 255 := by simpa using h.name name hn
    simp [extsSize, snData, svData, groupsData, sigData, ksData, alpnData, u16Bytes, h1]
    omega

theorem chExts_wf (cfg : Client.Config) (h : ClientOK cfg) (share : ByteArray)
    (hs : share.size ≤ 2048) : ExtsWF (chExts cfg share) := by
  have hg : cfg.share.group < 65536 := (group_sizes cfg.group).2.2
  have tp := h.tps
  have al := h.alpnSize
  have hsize := chExts_size cfg h share hs
  have hsg := sig_size cfg h
  have h1 : (⟨#[0]⟩ : ByteArray).size = 1 := rfl
  refine ⟨?_, ?_, by omega⟩ <;> unfold chExts chTail <;> rcases hn : cfg.serverName with _ | name
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro e (rfl | rfl | rfl | rfl | rfl | rfl) <;>
      simp [Extension.WF, ExtType.supportedVersions, ExtType.supportedGroups,
        ExtType.signatureAlgorithms, ExtType.keyShare, ExtType.alpn, ExtType.quicTransportParameters,
        svData, groupsData, sigData, ksData, alpnData, u16Bytes] <;> omega
  · have hname : name.utf8ByteSize ≤ 255 := by simpa using h.name name hn
    simp only [Array.toList_append, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro e (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      simp [Extension.WF, ExtType.serverName, ExtType.supportedVersions, ExtType.supportedGroups,
        ExtType.signatureAlgorithms, ExtType.keyShare, ExtType.alpn, ExtType.quicTransportParameters,
        snData, svData, groupsData, sigData, ksData, alpnData, u16Bytes, h1] <;> omega
  · simp [dupTypes, ExtType.supportedVersions, ExtType.supportedGroups,
      ExtType.signatureAlgorithms, ExtType.keyShare, ExtType.alpn, ExtType.quicTransportParameters]
  · simp [dupTypes, ExtType.serverName, ExtType.supportedVersions,
      ExtType.supportedGroups, ExtType.signatureAlgorithms, ExtType.keyShare, ExtType.alpn,
      ExtType.quicTransportParameters]

/-- The client's first flight: one ClientHello, which parses back to what the client meant. -/
theorem start_eq (cfg : Client.Config) (h : ClientOK cfg) (seed : Vector UInt8 32) :
    ∃ body, Client.start cfg seed =
        .ok (⟨.waitServerHello (cfg.share.clientGen (drawVec seed "key share" cfg.share.entropySize)).1
              (frameBytes HandshakeType.clientHello body), {}⟩,
            #[.send .initial (frameBytes HandshakeType.clientHello body)]) ∧
      body.size ≤ maxMessageSize ∧
      Parser.run Messages.clientHello body = .ok ⟨draw seed "client random" 32, ByteArray.empty,
        (cfg.suites.map (·.id)).toArray,
        chExts cfg (ofVector (cfg.share.clientGen (drawVec seed "key share" cfg.share.entropySize)).2)⟩ := by
  rcases hcg : cfg.share.clientGen (drawVec seed "key share" cfg.share.entropySize) with ⟨secret, sh⟩
  let share := ofVector sh
  have hs : share.size ≤ 2048 := by simp [share]; exact (group_sizes cfg.group).1
  let m : ClientHello := ⟨draw seed "client random" 32, ByteArray.empty, (cfg.suites.map (·.id)).toArray,
    chExts cfg share⟩
  have hwf : m.WF := {
    random := draw_size _ _ _
    sessionId := by simp [m]
    suites := by simp [m]; intro s _; exact suite_id_lt s
    suitesSize := by simp [m]; have := h.suites; omega
    exts := chExts_wf cfg h share hs }
  obtain ⟨body, hsz, hw, hr⟩ := rt_clientHello hwf
  have hbound : m.size ≤ 30000 := by
    have := chExts_size cfg h share hs
    have := h.suites
    simp only [ClientHello.size, m]
    simp
    omega
  refine ⟨body, ?_, by unfold maxMessageSize; omega, Reads.run hr⟩
  unfold Client.start
  rw [hcg]
  simp only
  rw [clientHello_eq cfg h _ share hs, frame_eq hw (by omega)]
  rfl

/-! ## Decoding the extensions -/

theorem reads_u16list1 {v : Nat} (hv : v < 65536) :
    ReadsAll u16List #[v] (u16Bytes v) := by
  have := Reads.many (p := Parser.u16) (out := fun x => beBytes 2 x) [v]
    (by simp only [List.mem_singleton, forall_eq]; exact ⟨Reads.uN hv, by simp⟩)
  have e : Writes.concatMap [v] (fun x => beBytes 2 x) = u16Bytes v := by
    simp [Writes.concatMap, ByteArray.empty_append, u16Bytes]
  rw [e] at this
  exact this

theorem decode_sv : decodeExt (Parser.vec8 u16List) svData = .ok #[Messages.tls13] := by
  have := Reads.vec8 (reads_u16list1 (v := Messages.tls13) (by decide)) (by simp [u16Bytes])
  have e : beBytes 1 (u16Bytes Messages.tls13).size ++ u16Bytes Messages.tls13 = svData := by
    simp [svData, u16Bytes]
  rw [e] at this
  exact Reads.run this

theorem decode_u16list {g : Nat} (hg : g < 65536) :
    decodeExt (Parser.vec16 u16List) (beBytes 2 2 ++ u16Bytes g) = .ok #[g] := by
  have := Reads.vec16 (reads_u16list1 hg) (by simp [u16Bytes])
  have e : beBytes 2 (u16Bytes g).size ++ u16Bytes g = beBytes 2 2 ++ u16Bytes g := by simp [u16Bytes]
  rw [e] at this
  exact Reads.run this

theorem reads_keyShareEntry {g : Nat} {key : ByteArray} (hg : g < 65536) (hk : key.size < 65536) :
    Reads keyShareEntry ⟨g, key⟩ (u16Bytes g ++ (beBytes 2 key.size ++ key)) := by
  have := (Reads.uN (n := 2) (v := g) (by simpa using hg)).bind
    (q := fun group => do let key ← Parser.opaque16; pure { group, key : KeyShareEntry })
    ((Reads.opaque16 hk).bind (q := fun key => pure ({ group := g, key } : KeyShareEntry)) (Reads.pure _))
  rw [ByteArray.append_empty] at this
  exact this

theorem decode_ks {g : Nat} {share : ByteArray} (hg : g < 65536) (hs : share.size < 60000) :
    decodeExt (Parser.vec16 (Parser.many keyShareEntry)) (ksData g share) = .ok #[⟨g, share⟩] := by
  have hm := Reads.many (p := keyShareEntry) (out := fun _ => u16Bytes g ++ (beBytes 2 share.size ++ share))
    [⟨g, share⟩] (by
      simp only [List.mem_singleton, forall_eq]
      exact ⟨reads_keyShareEntry hg (by omega), by simp [u16Bytes]⟩)
  have e : Writes.concatMap [(⟨g, share⟩ : KeyShareEntry)]
      (fun _ => u16Bytes g ++ (beBytes 2 share.size ++ share)) = u16Bytes g ++ (beBytes 2 share.size ++ share) := by
    simp [Writes.concatMap, ByteArray.empty_append]
  rw [e] at hm
  have := Reads.vec16 hm (by simp [u16Bytes]; omega)
  have e2 : beBytes 2 (u16Bytes g ++ (beBytes 2 share.size ++ share)).size ++
      (u16Bytes g ++ (beBytes 2 share.size ++ share)) = ksData g share := by
    simp only [ksData, ByteArray.size_append, u16Bytes, size_beBytes]
    congr 2
    omega
  rw [e2] at this
  exact Reads.run this

theorem decode_alpn {a : ByteArray} (h0 : 0 < a.size) (ha : a.size < 256) :
    decodeExt alpnList (alpnData a) = .ok #[a] := by
  have h2 : Reads ((fun p : ByteArray => if p.size == 0 then Parser.fail else pure p) a) a
      ByteArray.empty := by
    simp only [show (a.size == 0) = false by rw [beq_eq_false_iff_ne]; omega, Bool.false_eq_true,
      ↓reduceIte]
    exact Reads.pure a
  have hp := (Reads.opaque8 ha).bind (q := fun p : ByteArray => if p.size == 0 then Parser.fail else pure p) h2
  rw [ByteArray.append_empty] at hp
  have hm := Reads.many (out := fun _ => beBytes 1 a.size ++ a) [a]
    (by simp only [List.mem_singleton, forall_eq]; exact ⟨hp, by simp⟩)
  have e : Writes.concatMap [a] (fun _ => beBytes 1 a.size ++ a) = beBytes 1 a.size ++ a := by
    simp [Writes.concatMap, ByteArray.empty_append]
  rw [e] at hm
  have := Reads.vec16 hm (by simp; omega)
  have e2 : beBytes 2 (beBytes 1 a.size ++ a).size ++ (beBytes 1 a.size ++ a) = alpnData a := by
    simp only [alpnData, ByteArray.size_append, size_beBytes]
  rw [e2] at this
  exact Reads.run this

theorem find_chExts (cfg : Client.Config) (share : ByteArray) :
    find (chExts cfg share) ExtType.supportedVersions = some svData ∧
    find (chExts cfg share) ExtType.signatureAlgorithms = some (sigData cfg.schemes) ∧
    find (chExts cfg share) ExtType.alpn = some (alpnData cfg.alpn) ∧
    find (chExts cfg share) ExtType.quicTransportParameters = some cfg.transportParams ∧
    find (chExts cfg share) ExtType.keyShare = some (ksData cfg.share.group share) := by
  unfold chExts chTail
  rcases cfg.serverName with _ | name <;>
    simp [find, ExtType.serverName, ExtType.supportedVersions, ExtType.supportedGroups,
      ExtType.signatureAlgorithms, ExtType.keyShare, ExtType.alpn, ExtType.quicTransportParameters]

theorem find?_one {α : Type} (a : α) (p : α → Bool) :
    (#[a]).find? p = if p a then some a else none := by
  cases h : p a <;> simp [h]

theorem contains_one_bytes (x : ByteArray) : (#[x]).contains x = true := by simp

theorem contains_one_nat (x : Nat) : (#[x]).contains x = true := by simp

/-! ## The server's first flight -/

structure ServerOK (cfg : Server.Config) : Prop where
  alpnPos : 0 < cfg.alpn.size
  alpnSize : cfg.alpn.size < 256
  tps : cfg.transportParams.size ≤ 16384
  cert : cfg.certificate.size ≤ 30000

def shExts (g : Nat) (myShare : ByteArray) : Array Extension :=
  #[⟨ExtType.supportedVersions, u16Bytes Messages.tls13⟩,
    ⟨ExtType.keyShare, u16Bytes g ++ (beBytes 2 myShare.size ++ myShare)⟩]

def eeExts (alpn tps : ByteArray) : Array Extension :=
  #[⟨ExtType.alpn, alpnData alpn⟩, ⟨ExtType.quicTransportParameters, tps⟩]

def certMsg (cert : ByteArray) : Certificate := ⟨ByteArray.empty, #[⟨cert, ByteArray.empty⟩]⟩

/-- The server's flight for a ClientHello, given the bodies of its messages. -/
structure Flight where
  sh : ByteArray
  ee : ByteArray
  cert : ByteArray
  cv : ByteArray

namespace Flight

variable (f : Flight)

def shF : ByteArray := frameBytes HandshakeType.serverHello f.sh
def eeF : ByteArray := frameBytes HandshakeType.encryptedExtensions f.ee
def certF : ByteArray := frameBytes HandshakeType.certificate f.cert
def cvF : ByteArray := frameBytes HandshakeType.certificateVerify f.cv

end Flight

theorem server_onClientHello (cfg : Server.Config) (h : ServerOK cfg) (seed : Vector UInt8 32)
    (chB rC : ByteArray) (ids : Array Nat) (cfgC : Client.Config) (share : ByteArray)
    (hch : Parser.run Messages.clientHello chB = .ok ⟨rC, ByteArray.empty, ids, chExts cfgC share⟩)
    (hgroup : cfgC.share.group = cfg.share.group) (halpn : cfgC.alpn = cfg.alpn)
    (hshare : share.size = cfg.share.clientShareSize)
    {suite : Suite} (hsuite : cfg.suites.find? (ids.contains ·.id) = some suite)
    {myShare : Vector UInt8 cfg.share.serverShareSize} {k : Vector UInt8 cfg.share.secretSize}
    (hacc : cfg.share.serverRespond (drawVec seed "key share" cfg.share.entropySize) (toVecN _ share) =
      some (myShare, k))
    (hsch : cfg.scheme ∈ cfgC.schemes) (hlen : cfgC.schemes.length ≤ 100)
    (hsign : ∀ input, ∃ sig, cfg.scheme.sign cfg.signingKey seed input = .ok sig) :
    ∃ f : Flight, ∃ sig : ByteArray,
      let ch := frameBytes HandshakeType.clientHello chB
      let hs := KeySchedule.handshakeSecret (ofVector k)
      let hts := KeySchedule.handshakeTraffic hs (ch ++ f.shF)
      let t := ch ++ f.shF ++ f.eeF ++ f.certF
      cfg.scheme.sign cfg.signingKey seed (certVerifyInput true t) = .ok sig ∧
      let fin := KeySchedule.finishedData hts.server (t ++ f.cvF)
      let tFin := t ++ f.cvF ++ frameBytes HandshakeType.finished fin
      let ap := KeySchedule.applicationTraffic (KeySchedule.masterSecret hs) tFin
      Server.onClientHello cfg seed ⟨HandshakeType.clientHello, chB, ch⟩ =
        .ok (.waitFinished ⟨suite, hts.client, tFin, cfgC.transportParams⟩,
          #[.send .initial f.shF,
            .install .handshake suite { read := hts.client, write := hts.server },
            .send .handshake (f.eeF ++ f.certF ++ f.cvF ++ frameBytes HandshakeType.finished fin),
            .install .application suite { read := ap.client, write := ap.server }]) ∧
      Parser.run serverHello f.sh = .ok ⟨draw seed "server random" 32, ByteArray.empty, suite.id,
        shExts cfg.share.group (ofVector myShare)⟩ ∧
      Parser.run extensions f.ee = .ok (eeExts cfg.alpn cfg.transportParams) ∧
      Parser.run certificate f.cert = .ok (certMsg cfg.certificate) ∧
      Parser.run certificateVerify f.cv = .ok ⟨cfg.scheme.code, sig⟩ ∧
      f.sh.size ≤ maxMessageSize ∧ f.ee.size ≤ maxMessageSize ∧ f.cert.size ≤ maxMessageSize ∧
      f.cv.size ≤ maxMessageSize := by
  obtain ⟨hcs, hss, hgl⟩ := group_sizes cfg.group
  have hcs' : cfg.share.clientShareSize ≤ 2048 := hcs
  have hss' : cfg.share.serverShareSize ≤ 2048 := hss
  have hgl' : cfg.share.group < 65536 := hgl
  obtain ⟨hsv, hsig, halp, htp, hks⟩ := find_chExts cfgC share
  have hmy : (ofVector myShare).size ≤ 2048 := by simp; exact hss
  have hal := h.alpnSize
  have htps := h.tps
  -- ServerHello
  let mSH : ServerHello := ⟨draw seed "server random" 32, ByteArray.empty, suite.id,
    shExts cfg.share.group (ofVector myShare)⟩
  have hSH : mSH.WF := {
    random := draw_size _ _ _
    sessionId := by simp [mSH]
    suite := suite_id_lt suite
    exts := ⟨by
        simp only [mSH, shExts, List.mem_cons, List.not_mem_nil, or_false]
        rintro e (rfl | rfl) <;>
          simp [Extension.WF, ExtType.supportedVersions, ExtType.keyShare, u16Bytes]; omega,
      by simp [mSH, shExts, dupTypes, ExtType.supportedVersions, ExtType.keyShare],
      by simp [mSH, shExts, extsSize, u16Bytes]; omega⟩ }
  obtain ⟨shB, hshs, hshw, hshr⟩ := rt_serverHello hSH
  have hshsz : mSH.size ≤ 3000 := by simp [ServerHello.size, mSH, shExts, extsSize, u16Bytes]; omega
  -- EncryptedExtensions
  have hEE : ExtsWF (eeExts cfg.alpn cfg.transportParams) := ⟨by
      simp only [eeExts, List.mem_cons, List.not_mem_nil, or_false]
      rintro e (rfl | rfl) <;>
        simp [Extension.WF, ExtType.alpn, ExtType.quicTransportParameters, alpnData] <;> omega,
    by simp [eeExts, dupTypes, ExtType.alpn, ExtType.quicTransportParameters],
    by simp [eeExts, extsSize, alpnData]; omega⟩
  obtain ⟨eeB, hees, heew, heer⟩ := rt_extensions hEE
  have heesz : extsSize (eeExts cfg.alpn cfg.transportParams) ≤ 20000 := by
    simp [eeExts, extsSize, alpnData]; omega
  -- Certificate
  obtain ⟨certB, hcerts, hcertw, hcertr⟩ := rt_certificate (data := cfg.certificate) (by have := h.cert; omega)
  -- CertificateVerify
  let ch := frameBytes HandshakeType.clientHello chB
  let t := ch ++ frameBytes HandshakeType.serverHello shB ++ frameBytes HandshakeType.encryptedExtensions eeB ++
    frameBytes HandshakeType.certificate certB
  obtain ⟨sig, hsg⟩ := hsign (certVerifyInput true t)
  have hsz := Scheme.sign_size _ _ _ _ _ hsg
  obtain ⟨cvB, hcvs, hcvw, hcvr⟩ := rt_certificateVerify (m := ⟨cfg.scheme.code, sig⟩)
    (code_lt _) (show sig.size < 65536 by omega)
  refine ⟨⟨shB, eeB, certB, cvB⟩, sig, hsg, ?_, Reads.run hshr, Reads.run heer, Reads.run hcertr,
    Reads.run hcvr,
    show shB.size ≤ maxMessageSize by unfold maxMessageSize; omega,
    show eeB.size ≤ maxMessageSize by unfold maxMessageSize; omega,
    show certB.size ≤ maxMessageSize by unfold maxMessageSize; have := h.cert; omega,
    show cvB.size ≤ maxMessageSize by unfold maxMessageSize; dsimp only at hcvs; omega⟩
  -- The handler
  have hext1 : ext ExtType.supportedVersions (Writer.u16 Messages.tls13) =
      .ok ⟨ExtType.supportedVersions, u16Bytes Messages.tls13⟩ := ext_eq (Writes.uN (by decide))
  have hext2 : ext ExtType.keyShare (writeKeyShareEntry { group := cfg.share.group, key := ofVector myShare }) =
      .ok ⟨ExtType.keyShare, u16Bytes cfg.share.group ++ (beBytes 2 (ofVector myShare).size ++ ofVector myShare)⟩ :=
    ext_eq ((Writes.uN (n := 2) (by simpa using hgl)).bind ((Writes.bytes _).prefixed
      (show (ofVector myShare).size < 256 ^ 2 by rw [show (256 : Nat) ^ 2 = 65536 by rfl]; omega)))
  have hext3 : ext ExtType.alpn (writeAlpnList #[cfg.alpn]) = .ok ⟨ExtType.alpn, alpnData cfg.alpn⟩ :=
    ext_eq (writes_alpn hal)
  have hsigd := decode_sig cfgC.schemes hlen
  have hcontains : (cfgC.schemes.map Scheme.code).toArray.contains cfg.scheme.code = true := by
    simpa using List.mem_map_of_mem hsch
  simp only [mSH, shExts] at hshw
  simp only [eeExts] at heew
  simp only [t, ch] at hcvw hsg
  have hfin : ∀ b : ByteArray, b.size = 32 →
      frame HandshakeType.finished (Writer.bytes b) = .ok (frameBytes HandshakeType.finished b) :=
    fun b hb => frame_eq (Writes.bytes b) (by rw [hb]; decide)
  have hfd : ∀ a b, (KeySchedule.finishedData a b).size = 32 := fun a b => by
    simp [KeySchedule.finishedData]
  unfold Server.onClientHello
  simp only [hch, bind, Except.bind, pure, Except.pure, hsv, hsig, halp, htp, hks, require_some, decode_sv,
    hsigd, hcontains, hsg, decode_alpn h.alpnPos hal, halpn, hgroup,
    decode_ks hgl' (by rw [hshare]; omega), hsuite, hshare, hacc, hext1, hext2, hext3,
    ByteArray.size_empty, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, contains_one_bytes,
    contains_one_nat, find?_one, beq_self_eq_true,
    frame_eq hshw (by rw [show (256 : Nat) ^ 3 = 16777216 by rfl]; omega),
    frame_eq heew (by rw [show (256 : Nat) ^ 3 = 16777216 by rfl]; omega),
    frame_eq hcertw (by rw [show (256 : Nat) ^ 3 = 16777216 by rfl]; have := h.cert; omega),
    frame_eq hcvw (by rw [show (256 : Nat) ^ 3 = 16777216 by rfl]; dsimp only at hcvs; omega),
    hfin _ (hfd _ _)]
  rfl

theorem frames_one (t : UInt8) (b : ByteArray) : frameBytes t b = frames [(t, b)] := by
  show _ = frameBytes t b ++ ByteArray.empty
  rw [ByteArray.append_empty]

theorem split_one {t : UInt8} {b : ByteArray} (hb : b.size ≤ maxMessageSize) :
    splitMessages (ByteArray.empty ++ frameBytes t b) = .ok (#[⟨t, b, frameBytes t b⟩], ByteArray.empty) := by
  rw [ByteArray.empty_append, frames_one, splitMessages_frames _ (by simpa using hb)]
  simp [rawOf, ← frames_one]

theorem server_recv_clientHello (cfg : Server.Config) (seed : Vector UInt8 32) (b : ByteArray)
    (hb : b.size ≤ maxMessageSize) {p : Server.Phase} {o : Array Output}
    (hstep : Server.onClientHello cfg seed ⟨HandshakeType.clientHello, b, frameBytes HandshakeType.clientHello b⟩ =
      .ok (p, o)) :
    Server.recv cfg seed Server.init .initial (frameBytes HandshakeType.clientHello b) =
      .ok ({ phase := p, buffers := ({} : Buffers).set .initial ByteArray.empty }, o) := by
  unfold Server.recv
  rw [show (Server.init.buffers.get .initial) = ByteArray.empty from rfl, split_one hb]
  simp [bind, Except.bind, pure, Except.pure, Server.init, hstep]

theorem server_recv_finished (cfg : Server.Config) (seed : Vector UInt8 32) (pend : Server.Pending)
    (bufs : Buffers) (hbuf : bufs.get .handshake = ByteArray.empty) (b : ByteArray)
    (hb : b.size ≤ maxMessageSize) {p : Server.Phase} {o : Array Output}
    (hstep : Server.onFinished cfg pend ⟨HandshakeType.finished, b, frameBytes HandshakeType.finished b⟩ =
      .ok (p, o)) :
    Server.recv cfg seed ⟨.waitFinished pend, bufs⟩ .handshake (frameBytes HandshakeType.finished b) =
      .ok ({ phase := p, buffers := bufs.set .handshake ByteArray.empty }, o) := by
  unfold Server.recv
  rw [hbuf, split_one hb]
  simp [bind, Except.bind, pure, Except.pure, hstep]

/-! ## The client's steps -/

/-- `Client.recv`'s loop over the messages that arrived. -/
def handleAll {cfg : Client.Config} (level : Level) :
    Client.Phase cfg → Array Output → List RawMessage → Except Alert (Client.Phase cfg × Array Output)
  | p, out, [] => pure (p, out)
  | p, out, m :: ms => do
    let (p', o) ← Client.handle cfg p level m
    handleAll level p' (out ++ o) ms

theorem forIn_handle {cfg : Client.Config} (level : Level) :
    ∀ (ms : List RawMessage) (p : Client.Phase cfg) (out : Array Output),
      (forIn ms (p, out) fun m r => do
        let x ← Client.handle cfg r.1 level m
        pure (ForInStep.yield (x.1, r.2 ++ x.2)) : Except Alert (Client.Phase cfg × Array Output)) =
      handleAll level p out ms
  | [], p, out => rfl
  | m :: ms, p, out => by
    simp only [List.forIn_cons, handleAll, bind, Except.bind]
    rcases Client.handle cfg p level m with a | ⟨p', o⟩
    · rfl
    · simp only [pure, Except.pure]
      exact forIn_handle level ms p' (out ++ o)

theorem client_recv_eq {cfg : Client.Config} (s : Client.State cfg) (level : Level)
    (l : List (UInt8 × ByteArray)) (hbuf : s.buffers.get level = ByteArray.empty)
    (hnf : ∀ a, s.phase ≠ .failed a) (hl : ∀ m ∈ l, m.2.size ≤ maxMessageSize) :
    Client.recv s level (frames l) =
      (handleAll level s.phase #[] (l.map rawOf)).map
        fun (p, o) => (⟨p, s.buffers.set level ByteArray.empty⟩, o) := by
  unfold Client.recv
  rcases s with ⟨phase, bufs⟩
  simp only at hbuf hnf ⊢
  rw [hbuf, ByteArray.empty_append, splitMessages_frames l hl]
  simp only [bind, Except.bind]
  rw [← Array.forIn_toList, List.toList_toArray]
  have := forIn_handle (cfg := cfg) level (l.map rawOf) phase #[]
  simp only [bind, Except.bind] at this
  rw [this]
  rcases handleAll level phase #[] (l.map rawOf) with a | ⟨p, o⟩ <;> rfl

theorem find_suite {l : List Suite} {s : Suite} (h : s ∈ l) : l.find? (·.id == s.id) = some s := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    by_cases e : x = s
    · subst e; simp
    · have hx : (x.id == s.id) = false := by
        rw [beq_eq_false_iff_ne]; exact fun h' => e (suite_id_inj h')
      simp only [List.find?_cons, hx]
      exact ih (by simpa [Ne.symm e] using h)

theorem decode_u16 {v : Nat} (hv : v < 65536) : decodeExt Parser.u16 (u16Bytes v) = .ok v :=
  Reads.run (Reads.uN (n := 2) (by simpa using hv))

theorem client_onServerHello (cfg : Client.Config) (secret : cfg.share.ClientSecret) (ch shB : ByteArray)
    {suite : Suite} (hsuite : suite ∈ cfg.suites) {random : ByteArray} (hr : random ≠ helloRetryRandom)
    (myShare : Vector UInt8 cfg.share.serverShareSize) {k : Vector UInt8 cfg.share.secretSize}
    (hk : cfg.share.clientFinish secret myShare = some k)
    (hsh : Parser.run serverHello shB =
      .ok ⟨random, ByteArray.empty, suite.id, shExts cfg.share.group (ofVector myShare)⟩) :
    Client.onServerHello cfg secret ch ⟨HandshakeType.serverHello, shB, frameBytes HandshakeType.serverHello shB⟩ =
      .ok (.waitEncryptedExtensions ⟨suite, KeySchedule.handshakeSecret (ofVector k),
          KeySchedule.handshakeTraffic (KeySchedule.handshakeSecret (ofVector k))
            (ch ++ frameBytes HandshakeType.serverHello shB),
          ch ++ frameBytes HandshakeType.serverHello shB⟩,
        #[.install .handshake suite
          { read := (KeySchedule.handshakeTraffic (KeySchedule.handshakeSecret (ofVector k))
              (ch ++ frameBytes HandshakeType.serverHello shB)).server,
            write := (KeySchedule.handshakeTraffic (KeySchedule.handshakeSecret (ofVector k))
              (ch ++ frameBytes HandshakeType.serverHello shB)).client }]) := by
  obtain ⟨hcs, hss, hgl⟩ := group_sizes cfg.group
  have hss' : cfg.share.serverShareSize ≤ 2048 := hss
  have hgl' : cfg.share.group < 65536 := hgl
  have hfv : find (shExts cfg.share.group (ofVector myShare)) ExtType.supportedVersions =
      some (u16Bytes Messages.tls13) := by simp [find, shExts, ExtType.supportedVersions, ExtType.keyShare]
  have hfk : find (shExts cfg.share.group (ofVector myShare)) ExtType.keyShare =
      some (u16Bytes cfg.share.group ++ (beBytes 2 (ofVector myShare).size ++ ofVector myShare)) := by
    simp [find, shExts, ExtType.supportedVersions, ExtType.keyShare]
  have hdk : decodeExt keyShareEntry
      (u16Bytes cfg.share.group ++ (beBytes 2 (ofVector myShare).size ++ ofVector myShare)) =
      .ok ⟨cfg.share.group, ofVector myShare⟩ :=
    Reads.run (reads_keyShareEntry hgl' (by simp; omega))
  unfold Client.onServerHello
  simp only [hsh, bind, Except.bind, pure, Except.pure, hr, beq_iff_eq, ↓reduceIte, ByteArray.size_empty,
    bne_self_eq_false, Bool.false_eq_true, find_suite hsuite, require_some, hfv, hfk,
    decode_u16 (v := Messages.tls13) (by decide), hdk]
  simp only [Cryptlib.Util.Bytes.size_ofVector, bne_self_eq_false, Bool.or_false, Bool.false_eq_true,
    ↓reduceIte, Cryptlib.Util.Bytes.toVecN_ofVector, hk, require_some]

theorem find_eeExts (alpn tps : ByteArray) :
    find (eeExts alpn tps) ExtType.alpn = some (alpnData alpn) ∧
    find (eeExts alpn tps) ExtType.quicTransportParameters = some tps := by
  simp [find, eeExts, ExtType.alpn, ExtType.quicTransportParameters]

theorem get0 {α : Type} [Inhabited α] (a : α) : (#[a])[0]! = a := rfl

theorem get0? {α : Type} (a : α) : (#[a])[0]? = some a := rfl

theorem ctEq_self (b : ByteArray) : ctEq b b = true :=
  (Cryptlib.Util.ConstantTime.ctEq_iff b b).mpr rfl

theorem client_flight (cfg : Client.Config) (ctx : Client.HsCtx) (sch : Scheme)
    (sk seed : Vector UInt8 32) (eeB certB cvB tps sig : ByteArray) {leaf : X509.Leaf}
    {certData : ByteArray}
    (hee : Parser.run extensions eeB = .ok (eeExts cfg.alpn tps))
    (halpn0 : 0 < cfg.alpn.size) (halpn : cfg.alpn.size < 256)
    (hcert : Parser.run certificate certB = .ok (certMsg certData))
    (hleaf : X509.parseLeaf certData = .ok leaf)
    (hkey : leaf.key = some (sch.authKey sk))
    (hsch : sch ∈ cfg.schemes)
    (hpin : KeySchedule.hash leaf.spki ∈ cfg.pins)
    (hsign : sch.sign sk seed (certVerifyInput true (ctx.transcript ++
      frameBytes HandshakeType.encryptedExtensions eeB ++ frameBytes HandshakeType.certificate certB)) =
      .ok sig)
    (hcv : Parser.run certificateVerify cvB = .ok ⟨sch.code, sig⟩) :
    let t := ctx.transcript ++ frameBytes HandshakeType.encryptedExtensions eeB ++
      frameBytes HandshakeType.certificate certB ++ frameBytes HandshakeType.certificateVerify cvB
    let fin := KeySchedule.finishedData ctx.secrets.server t
    let tFin := t ++ frameBytes HandshakeType.finished fin
    let ap := KeySchedule.applicationTraffic (KeySchedule.masterSecret ctx.hs) tFin
    ∃ est : Client.Established cfg, est.peerTransportParams = tps ∧
      handleAll .handshake (.waitEncryptedExtensions ctx) #[]
        [⟨HandshakeType.encryptedExtensions, eeB, frameBytes HandshakeType.encryptedExtensions eeB⟩,
         ⟨HandshakeType.certificate, certB, frameBytes HandshakeType.certificate certB⟩,
         ⟨HandshakeType.certificateVerify, cvB, frameBytes HandshakeType.certificateVerify cvB⟩,
         ⟨HandshakeType.finished, fin, frameBytes HandshakeType.finished fin⟩] =
      .ok (.connected est,
        #[.send .handshake (frameBytes HandshakeType.finished
            (KeySchedule.finishedData ctx.secrets.client tFin)),
          .install .application ctx.suite { read := ap.server, write := ap.client }]) := by
  intro t fin tFin ap
  obtain ⟨hfa, hft⟩ := find_eeExts cfg.alpn tps
  have hvalid := Scheme.verify_sign _ _ _ _ _ hsign
  have hsc : cfg.schemes.contains (sch.authKey sk).scheme = true := by
    rw [Scheme.authKey_scheme]; simpa using hsch
  have hcode : ((sch.code != (sch.authKey sk).scheme.code) = true) = False := by
    rw [Scheme.authKey_scheme]; simp
  have hfin : ∀ b : ByteArray, b.size = 32 →
      frame HandshakeType.finished (Writer.bytes b) = .ok (frameBytes HandshakeType.finished b) :=
    fun b hb => frame_eq (Writes.bytes b) (by rw [hb]; decide)
  have hfd : ∀ a b, (KeySchedule.finishedData a b).size = 32 := fun a b => by
    simp [KeySchedule.finishedData]
  simp only [handleAll, Client.handle, Client.onEncryptedExtensions, Client.onCertificate,
    Client.onCertificateVerify, Client.onFinished, bind, Except.bind, pure, Except.pure, hee, hfa, hft,
    decode_alpn halpn0 halpn, require_some, beq_self_eq_true, ↓reduceIte, hcert, certMsg, hleaf, hkey,
    hpin, hcv, hvalid, List.size_toArray, List.length_singleton, get0, hsc, hcode,
    bne_self_eq_false, Bool.or_false, Bool.false_eq_true, ByteArray.size_empty, get0?, dite_true,
    Bool.not_true, hfin _ (hfd _ _), ctEq_self, fin, t, tFin, ap]
  exact ⟨_, rfl, rfl⟩

theorem server_onFinished (cfg : Server.Config) (pend : Server.Pending) :
    ∃ est : Server.Established, est.peerTransportParams = pend.peerTransportParams ∧
      Server.onFinished cfg pend ⟨HandshakeType.finished,
        KeySchedule.finishedData pend.clientHandshake pend.transcript,
        frameBytes HandshakeType.finished (KeySchedule.finishedData pend.clientHandshake pend.transcript)⟩ =
      .ok (.connected est, #[]) := by
  unfold Server.onFinished
  simp only [ctEq_self, dite_true]
  exact ⟨_, rfl, rfl⟩

theorem finishedData_size (a b : ByteArray) : (KeySchedule.finishedData a b).size = 32 := by
  simp [KeySchedule.finishedData]

theorem handleAll_one {cfg : Client.Config} (level : Level) (p : Client.Phase cfg) (out : Array Output)
    (m : RawMessage) :
    handleAll level p out [m] = (Client.handle cfg p level m).map fun (p', o) => (p', out ++ o) := by
  simp only [handleAll, bind, Except.bind, pure, Except.pure]
  rcases Client.handle cfg p level m with a | ⟨p', o⟩ <;> rfl

theorem client_recv_one {cfg : Client.Config} (s : Client.State cfg) (level : Level) (t : UInt8)
    (b : ByteArray) (hbuf : s.buffers.get level = ByteArray.empty) (hnf : ∀ a, s.phase ≠ .failed a)
    (hb : b.size ≤ maxMessageSize) :
    Client.recv s level (frameBytes t b) =
      (Client.handle cfg s.phase level ⟨t, b, frameBytes t b⟩).map
        fun (p, o) => (⟨p, s.buffers.set level ByteArray.empty⟩, #[] ++ o) := by
  rw [frames_one, client_recv_eq s level [(t, b)] hbuf hnf (by simpa using hb)]
  simp only [List.map_cons, List.map_nil, rawOf, handleAll_one, ← frames_one]
  rcases Client.handle cfg s.phase level ⟨t, b, frameBytes t b⟩ with a | ⟨p', o⟩ <;> rfl

theorem frames_four (a b c d : UInt8 × ByteArray) :
    frames [a, b, c, d] = frameBytes a.1 a.2 ++ frameBytes b.1 b.2 ++ frameBytes c.1 c.2 ++
      frameBytes d.1 d.2 := by
  simp [frames, ByteArray.append_assoc, ByteArray.append_empty]

/-! ## The handshake -/

/-- What an honest client and server, and their entropy, satisfy. -/
structure Honest (cfgC : Client.Config) (cfgS : Server.Config) (seedC seedS : Vector UInt8 32) :
    Prop where
  client : ClientOK cfgC
  server : ServerOK cfgS
  group : cfgC.group = cfgS.group
  alpn : cfgC.alpn = cfgS.alpn
  suite : ∃ s ∈ cfgS.suites, s ∈ cfgC.suites
  /-- The key exchange agrees for this entropy (always, for X25519). -/
  reliable : cfgC.share.Reliable (drawVec seedC "key share" cfgC.share.entropySize)
    (drawVec seedS "key share" cfgC.share.entropySize)
  /-- The server accepts the client's share. -/
  accepted : (cfgC.share.serverRespond (drawVec seedS "key share" cfgC.share.entropySize)
    (cfgC.share.clientGen (drawVec seedC "key share" cfgC.share.entropySize)).2).isSome
  /-- The server's random is not the one that marks a HelloRetryRequest. -/
  random : draw seedS "server random" 32 ≠ helloRetryRandom
  /-- The server's certificate holds its signing key, and the client pins it. -/
  certificate : ∃ leaf : X509.Leaf, X509.parseLeaf cfgS.certificate = .ok leaf ∧
    leaf.key = some (cfgS.scheme.authKey cfgS.signingKey) ∧
    KeySchedule.hash leaf.spki ∈ cfgC.pins
  /-- The client accepts the server's signature scheme. -/
  scheme : cfgS.scheme ∈ cfgC.schemes
  /-- The server's signer does not give up: always so for Ed25519 (`Scheme.sign_ed25519`), with
  negligible exceptions for ML-DSA. -/
  signs : ∀ input, ∃ sig, cfgS.scheme.sign cfgS.signingKey seedS input = .ok sig

theorem handshake_correct (cfgC : Client.Config) (cfgS : Server.Config) (seedC seedS : Vector UInt8 32)
    (h : Honest cfgC cfgS seedC seedS) :
    ∃ c oc s os, run cfgC cfgS seedC seedS = .ok (c, oc, s, os) ∧
      c.established?.map (·.peerTransportParams) = some cfgS.transportParams ∧
      s.established?.map (·.peerTransportParams) = some cfgC.transportParams ∧
      (installsOf oc).map (·.1) = [.handshake, .application] ∧
      installsOf oc = (installsOf os).map fun (l, su, k) => (l, su, { read := k.write, write := k.read }) := by
  obtain ⟨hC, hS, hg, ha, ⟨s0, hs0S, hs0C⟩, hrel, hacc, hrand, ⟨leaf, hleaf, hkey, hpin⟩, hsch,
    hsign⟩ := h
  rcases cfgC with ⟨gC, suitesC, alpnC, tpC, pinsC, schemesC, nameC⟩
  simp only at hg ha hs0C hpin hsch ⊢
  subst hg ha
  -- The ClientHello
  obtain ⟨chB, hstart, hchsz, hchparse⟩ := start_eq _ hC seedC
  -- The cipher suite the server picks
  let ids := (suitesC.map (·.id)).toArray
  obtain ⟨suite, hfind⟩ : ∃ suite, cfgS.suites.find? (ids.contains ·.id) = some suite := by
    refine Option.isSome_iff_exists.mp (List.find?_isSome.mpr ⟨s0, hs0S, ?_⟩)
    simp [ids]; exact ⟨s0, hs0C, rfl⟩
  have hsuiteC : suite ∈ suitesC := by
    have := List.find?_some hfind
    simp only [ids, Array.contains_iff_mem, List.mem_toArray, List.mem_map] at this
    obtain ⟨t, ht, hid⟩ := this
    simpa [suite_id_inj hid] using ht
  -- The key exchange
  obtain ⟨⟨myShare, k⟩, hresp⟩ := Option.isSome_iff_exists.mp hacc
  have hk := cfgS.share.agree _ _ hrel myShare k hresp
  -- The server's flight
  have hacc' : cfgS.share.serverRespond (drawVec seedS "key share" cfgS.share.entropySize)
      (toVecN _ (ofVector (cfgS.share.clientGen (drawVec seedC "key share" cfgS.share.entropySize)).2)) =
      some (myShare, k) := by
    rw [Cryptlib.Util.Bytes.toVecN_ofVector]; exact hresp
  obtain ⟨f, sig, hsg, hon, hshp, heep, hcertp, hcvp, hshs, hees, hcerts, hcvs⟩ :=
    server_onClientHello cfgS hS seedS chB (draw seedC "client random" 32) ids _ _ hchparse rfl rfl
      (by simp) hfind hacc' hsch hC.schemes hsign
  have hs1 := server_recv_clientHello cfgS seedS chB hchsz hon
  -- The client takes the ServerHello
  let cfgC : Client.Config := ⟨cfgS.group, suitesC, cfgS.alpn, tpC, pinsC, schemesC, nameC⟩
  have hsh := client_onServerHello cfgC (cfgS.share.clientGen (drawVec seedC "key share" cfgS.share.entropySize)).1
    (frameBytes HandshakeType.clientHello chB) f.sh hsuiteC hrand myShare hk hshp
  have hc1 := client_recv_one (cfg := cfgC)
    ⟨.waitServerHello (cfgS.share.clientGen (drawVec seedC "key share" cfgS.share.entropySize)).1
      (frameBytes HandshakeType.clientHello chB), {}⟩ .initial HandshakeType.serverHello f.sh rfl
    (by intro a h; cases h) hshs
  simp only [Client.handle, beq_self_eq_true, ↓reduceIte, hsh] at hc1
  -- The client takes the rest of the flight
  obtain ⟨estC, hestC, hflight⟩ := client_flight cfgC
    ⟨suite, KeySchedule.handshakeSecret (ofVector k),
      KeySchedule.handshakeTraffic (KeySchedule.handshakeSecret (ofVector k))
        (frameBytes HandshakeType.clientHello chB ++ frameBytes HandshakeType.serverHello f.sh),
      frameBytes HandshakeType.clientHello chB ++ frameBytes HandshakeType.serverHello f.sh⟩
    cfgS.scheme cfgS.signingKey seedS f.ee f.cert f.cv cfgS.transportParams sig heep hS.alpnPos
    hS.alpnSize hcertp hleaf hkey hsch hpin hsg hcvp
  have hc2 := client_recv_eq (cfg := cfgC)
    ⟨.waitEncryptedExtensions ⟨suite, KeySchedule.handshakeSecret (ofVector k),
      KeySchedule.handshakeTraffic (KeySchedule.handshakeSecret (ofVector k))
        (frameBytes HandshakeType.clientHello chB ++ frameBytes HandshakeType.serverHello f.sh),
      frameBytes HandshakeType.clientHello chB ++ frameBytes HandshakeType.serverHello f.sh⟩,
      ({} : Buffers).set .initial ByteArray.empty⟩ .handshake
    [(HandshakeType.encryptedExtensions, f.ee), (HandshakeType.certificate, f.cert),
     (HandshakeType.certificateVerify, f.cv),
     (HandshakeType.finished, KeySchedule.finishedData
        (KeySchedule.handshakeTraffic (KeySchedule.handshakeSecret (ofVector k))
          (frameBytes HandshakeType.clientHello chB ++ frameBytes HandshakeType.serverHello f.sh)).server
        (frameBytes HandshakeType.clientHello chB ++ frameBytes HandshakeType.serverHello f.sh ++
          frameBytes HandshakeType.encryptedExtensions f.ee ++ frameBytes HandshakeType.certificate f.cert ++
          frameBytes HandshakeType.certificateVerify f.cv))]
    rfl (by intro a h; cases h) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro m (rfl | rfl | rfl | rfl) <;> first | assumption | (rw [finishedData_size]; decide))
  simp only [frames_four, List.map_cons, List.map_nil, rawOf, hflight] at hc2
  -- The server takes the client's Finished
  obtain ⟨estS, hestS, hfinS⟩ := server_onFinished cfgS
    ⟨suite, (KeySchedule.handshakeTraffic (KeySchedule.handshakeSecret (ofVector k))
        (frameBytes HandshakeType.clientHello chB ++ f.shF)).client,
      frameBytes HandshakeType.clientHello chB ++ f.shF ++ f.eeF ++ f.certF ++ f.cvF ++
        frameBytes HandshakeType.finished (KeySchedule.finishedData
          (KeySchedule.handshakeTraffic (KeySchedule.handshakeSecret (ofVector k))
            (frameBytes HandshakeType.clientHello chB ++ f.shF)).server
          (frameBytes HandshakeType.clientHello chB ++ f.shF ++ f.eeF ++ f.certF ++ f.cvF)),
      tpC⟩
  have hs2 := server_recv_finished cfgS seedS _ (({} : Buffers).set .initial ByteArray.empty) rfl _
    (by rw [finishedData_size]; decide) hfinS
  simp only [Flight.shF, Flight.eeF, Flight.certF, Flight.cvF] at hon hs1 hs2 hestS ⊢
  simp only [run, hstart, bind, Except.bind, sendsOf, List.filterMap_cons,
    List.filterMap_nil, deliver, hs1, pure, Except.pure, Array.toList_append, List.append_nil, hc1, hc2,
    Except.map, List.nil_append, List.cons_append]
  simp only [hs2]
  refine ⟨_, _, _, _, rfl, ?_, ?_, ?_, ?_⟩
  · simp [Client.State.established?, hestC]
  · simp [Server.State.established?, hestS]
  · simp [installsOf]
  · simp [installsOf]

end LeanTLS.Handshake

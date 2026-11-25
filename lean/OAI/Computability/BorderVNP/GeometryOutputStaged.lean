import OAI.Computability.BorderVNP.GeometryOutputTable
import OAI.Computability.BorderVNP.GeometryAdvicePrepare
import OAI.Computability.BorderVNP.DiagonalResidueRAMReplay

/-! # Complete native geometry frame evaluation

A single literal packet supplies the gate table, input addresses and all output
references. The machine evaluates the shared table once, checks its validity
wire, and packs every selected word. Geometry inputs are public, so the
returning execution is unique even on arbitrary ambient choice tapes.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace GeometryOutput

open VPVNP VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM RoutingISA
open GeometryFrameEncoding DiagonalResidueRAM

variable {w u o b : ℕ}

/-- Count the words encoding the header, program, input list, and output directory. -/
def packetCount (u k o b : ℕ) : ℕ := 6+3*k+u+(o*b+1)

/-- The whole geometry stage on the ordinary native ISA. -/
def staged : Code := .seq GeometryAdvicePrepare.stage code

/-- Exact cost including unpacking, shared gate evaluation, and output scatter. -/
def stagedTicks (w u k o b : ℕ) : ℕ :=
  GeometryAdvicePrepare.stageTicks u k (packetCount u k o b) w + ticks o b

/-- The instruction bound charges each literal bit, gate, query bit and output bit. -/
theorem stagedTicks_le (w u k o b : ℕ) : stagedTicks w u k o b ≤
    8*packetCount u k o b*(w+1) + 7*u + 14*k + 15*o*(b+1) + 97 := by
  have hp := DiagonalTallyBits.ticks_le (packetCount u k o b) w
  have hs := ticks_le o b
  unfold stagedTicks GeometryAdvicePrepare.stageTicks GeometryAdvicePrepare.prepareTicks
  omega

/-- The concrete placements used by the two stages. -/
structure Placement (pub : Arg → Word w) (l : Layout) (base start dense : ℕ)
    (src : Fin u → ℕ) (t : Table (Fin u ⊕ Fin 0) o b) : Prop where
  /-- All input and program bytes fit the staging layout. -/
  input : GeometryAdvicePrepare.Layout base start dense src t.size w (packetCount u t.size o b)
  /-- Output packing uses a bounded and disjoint workspace. -/
  output : l.Fits w
  /-- One result word for each requested output. -/
  count : l.count = o
  /-- The declared word width is the geometry pin width. -/
  width : l.width = b
  /-- The output references follow the ordinary gate and input packet. -/
  directory : l.refs = start+(6+3*t.size+u)
  /-- The temporary gather cannot overwrite any output source. -/
  temporary : l.temp+o*b ≤ base ∨ gateBase base u 0+t.size ≤ l.temp
  /-- The complete geometry header fits in physical address space. -/
  frameFit : (pub 0).val+108 < 2^w
  /-- Each output header field survives packet materialization and gate evaluation. -/
  frameOutside : ∀ i, 104 ≤ i → i ≤ 108 →
    ((pub 0).val+i < base ∨ gateBase base u 0+t.size ≤ (pub 0).val+i) ∧
    ((pub 0).val+i < start ∨ start+packetCount u t.size o b ≤ (pub 0).val+i)

/-- The packed gate and output advice and the input query exist at real memory addresses. -/
structure Input (pub : Arg → Word w) (m : Memory w) (l : Layout) (base start dense : ℕ)
    (src : Fin u → ℕ) (t : Table (Fin u ⊕ Fin 0) o b) (x : Fin u → Bool) : Prop where
  /-- The first packer reads its four true frame words. -/
  packFrame : GeometryAdvicePrepare.frame98 pub m dense start (packetCount u t.size o b)
  /-- The output processor reads its five true frame words. -/
  outputFrame : l.loaded pub m
  /-- The delivered literal packet holds the gate records and the appended output directory. -/
  bits : DiagonalTallyBits.WordsAt m dense
    ((payload w base start t.circuit src ++ referenceWords w base t).map BurstRAM.wordBits)
  /-- The indirect input list points to the actual query bits. -/
  sources : ∀ i, m (src i) = wordBit w (x i)

/-- The complete output array and all memory outside the four writable intervals. -/
structure Result (m mz : Memory w) (l : Layout) (base start : ℕ)
    (t : Table (Fin u ⊕ Fin 0) o b) (x : Fin u → Bool) : Prop where
  /-- Packed word values agree with the original high-to-low geometry bit numbering. -/
  words : ∀ i : Fin o, mz (l.dest+i.val) =
    word w (ParseBatchSort.value fun j => (t.bit i j).read id (Sum.elim x Fin.elim0)
      (t.program.run (Sum.elim x Fin.elim0)))
  /-- Valuations, packet words, gather bits and packed outputs are the sole mutable regions. -/
  outside : ∀ a, (a < base ∨ gateBase base u 0+t.size ≤ a) →
    (a < start ∨ start+packetCount u t.size o b ≤ a) →
    (a < l.temp ∨ l.temp+o*b ≤ a) → (a < l.dest ∨ l.dest+o ≤ a) → mz a = m a

private theorem stage_inputs (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (l : Layout) (base start dense : ℕ) (src : Fin u → ℕ)
    (t : Table (Fin u ⊕ Fin 0) o b) (x : Fin u → Bool)
    (L : Placement pub l base start dense src t) (h : Input pub m l base start dense src t x) :
    ∃ z mz, Exact pub mac GeometryAdvicePrepare.stage s m []
      (GeometryAdvicePrepare.stageTicks u t.size (packetCount u t.size o b) w) z mz ∧
      l.loaded pub mz ∧ Words mz l.refs (referenceWords w base t) ∧
      Knows base x Fin.elim0 (t.program.run (Sum.elim x Fin.elim0)) mz ∧
      ∀ a, (a < base ∨ gateBase base u 0+t.size ≤ a) →
        (a < start ∨ start+packetCount u t.size o b ≤ a) → mz a = m a := by
  obtain ⟨z,mz,r,_,_,known,packet,keep⟩ := GeometryAdvicePrepare.stage_runs pub mac s m base start dense src
    t.circuit x (referenceWords w base t)
    (by simpa [packetCount] using L.input) (by have := L.frameFit; omega)
    (by simpa [packetCount] using h.packFrame) h.bits h.sources
  have keep' : ∀ a, (a < base ∨ gateBase base u 0+t.size ≤ a) →
        (a < start ∨ start+packetCount u t.size o b ≤ a) → mz a = m a := by
    simpa only [packetCount,referenceWords_length] using keep
  have field (i : ℕ) (lo : 104 ≤ i) (hi : i ≤ 108) : mz ((pub 0).val+i) = m ((pub 0).val+i) :=
    keep' _ (L.frameOutside i lo hi).1 (L.frameOutside i lo hi).2
  refine ⟨z,mz,by simpa only [packetCount,referenceWords_length] using r,?_,?_,known,keep'⟩
  · unfold Layout.loaded
    simp only [field 104 (by decide) (by decide),field 105 (by decide) (by decide),
      field 106 (by decide) (by decide),field 107 (by decide) (by decide),field 108 (by decide) (by decide)]
    exact h.outputFrame
  · simpa only [L.directory,payload_length] using (Words.append packet).2

/-- All geometrical words are obtained by native execution of the staged literal reader,
with no choices and a single gate scan for all result coordinates. -/
theorem staged_runs (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w)
    (m : Memory w) (l : Layout) (base start dense : ℕ) (src : Fin u → ℕ)
    (t : Table (Fin u ⊕ Fin 0) o b) (x : Fin u → Bool)
    (L : Placement pub l base start dense src t) (h : Input pub m l base start dense src t x)
    (valid : validBit t (Sum.elim x Fin.elim0) = true) :
    ∃ z mz, Exact pub mac staged s m [] (stagedTicks w u t.size o b) z mz ∧ Result m mz l base start t x := by
  obtain ⟨a,ma,pre,frame,refs,knows,keep⟩ := stage_inputs pub mac s m l base start dense src t x L h
  have fit : gateBase base u 0+t.size ≤ 2^w :=
    L.input.valuation.trans (Nat.le_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_right ..) L.input.packed))
  obtain ⟨z,run⟩ := table_runs pub mac a ma l base t x Fin.elim0 L.count L.width L.output frame
    L.frameFit refs knows fit L.temporary valid
  let ys := chunks t (Sum.elim x Fin.elim0)
  refine ⟨z,resultMemory ma l ys,?_,?_⟩
  · simpa only [staged,stagedTicks,L.count,L.width,List.nil_append] using pre.seq run
  · constructor
    · intro i
      exact (resultMemory_word ma l ys ⟨i.val,by simp [ys]⟩).trans
        (congrArg (word w) (chunk_value t _ i))
    · intro j hv hp ht hd
      exact (resultMemory_outside ma l ys j (by simpa [ys] using hd)
        (by simpa only [ys,chunks_flatten_length] using ht)).trans (keep j hv hp)

/-- A false validity bit admits no execution through the complete geometry stage.
The shared gate evaluator consumes zero private guesses on its unique returning path. -/
theorem staged_invalid_no_run (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (l : Layout) (base start dense : ℕ) (src : Fin u → ℕ)
    (t : Table (Fin u ⊕ Fin 0) o b) (x : Fin u → Bool)
    (L : Placement pub l base start dense src t) (h : Input pub m l base start dense src t x)
    (invalid : validBit t (Sum.elim x Fin.elim0) = false) {es z mz} :
    ¬ Runs pub mac staged s m es z mz := by
  obtain ⟨a,ma,⟨ds,pre,tr⟩,frame,refs,knows,_⟩ := stage_inputs pub mac s m l base start dense src t x L h
  have fit : gateBase base u 0+t.size ≤ 2^w :=
    L.input.valuation.trans (Nat.le_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_right ..) L.input.packed))
  intro r
  cases r with
  | atom atomic => cases atomic
  | seq first rest =>
    rename_i ds' z' m' fs
    obtain ⟨rfl,rfl,rfl⟩ := unique_returns (c := GeometryAdvicePrepare.stage) (by decide) pre first
      (tail := ds'.flatMap TeamRAM.Event.choices) (tail' := []) (by rw [tr.2.1]; simp)
    exact table_invalid_no_run pub mac _ _ l base t x Fin.elim0 L.output frame
      L.frameFit refs knows fit invalid rest

set_option maxRecDepth 4000 in
/-- On a valid packet, native execution accepts exactly the unique chronological
trace supplied by the returning no-choice path, including the previous value of each store. -/
theorem staged_execute_iff {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {s m es z mz n} (r : Runs pub mac staged s m es z mz) (tr : TraceOK es [] n)
    (tape : List (List Bool)) (fs : List (TeamRAM.Event w)) :
    TeamRAM.execute (staged.program.fetch pub mac) ⟨0,s⟩ m tape = some fs ↔
      fs = es ∧ tape = es.map TeamRAM.Event.choices := by
  rw [Code.execute_iff_runs (c := staged) (by decide)]
  constructor
  · rintro ⟨⟨_,_,run⟩,rfl⟩
    obtain ⟨rfl,_,_⟩ := unique_returns (c := staged) (by decide) r run
      (tail := fs.flatMap TeamRAM.Event.choices) (tail' := []) (by rw [tr.2.1]; simp)
    exact ⟨rfl,rfl⟩
  · rintro ⟨rfl,rfl⟩
    exact ⟨⟨z,mz,r⟩,rfl⟩

/-- A native accepting event stream exists exactly when the circuit's validity
output is true, with all circuit inputs supplied by the shared placement. -/
theorem staged_accepts_iff (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (l : Layout) (base start dense : ℕ) (src : Fin u → ℕ)
    (t : Table (Fin u ⊕ Fin 0) o b) (x : Fin u → Bool)
    (L : Placement pub l base start dense src t) (h : Input pub m l base start dense src t x) :
    (∃ tape es, TeamRAM.execute (staged.program.fetch pub mac) ⟨0,s⟩ m tape = some es) ↔
      validBit t (Sum.elim x Fin.elim0) = true := by
  constructor
  · rintro ⟨_,_,he⟩
    obtain ⟨⟨_,_,run⟩,_⟩ := (Code.execute_iff_runs (c := staged) (by decide)).mp he
    cases hflag : validBit t (Sum.elim x Fin.elim0) with
    | false => exact (staged_invalid_no_run pub mac s m l base start dense src t x L h hflag run).elim
    | true => rfl
  · intro hflag
    obtain ⟨_,_,⟨es,run,_⟩,_⟩ := staged_runs pub mac s m l base start dense src t x L h hflag
    exact ⟨_,es,run.execute⟩

end GeometryOutput

end BorderVNP
end Computability
end OAI

import OAI.Computability.VPVNP.LiveHeaderSparseLayout
import OAI.Computability.VPVNP.LiveHeaderCopyDispatch

/-!
# Constructing the auxiliary header descriptors on the live RAM

A fixed straight-line call reads the two exterior cut lengths from live scratch
memory. It calculates all seven packed ends and sparse target addresses, then
writes the twenty-one descriptor words into a contiguous table. All reads precede
the first table write.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveAuxiliaryDescriptorInit

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM PrimedInputRAM LiveAuxiliaryHeaders LiveHeaderCopyDispatch
open scoped Fin.CommRing

variable {w : ℕ}

/-- Straight-line descriptor-initializer operations over 32 registers and 14 public operands. -/
abbrev Ops := List (Op 32 14)

/-- The initializer's public operands, including header dimensions, the histogram length,
workspace addresses, and the seven source array bases. -/
def data (L : Lengths) (N : ℕ) (shadow table lengthsSource : Word w) (source : Fin 7 → Word w) :
    Fin 14 → Word w :=
  ![(L.index : Word w), (L.advice : Word w), (L.cutCapacity : Word w), (N : Word w), shadow, table,
    lengthsSource, source 0, source 1, source 2, source 3, source 4, source 5, source 6]

private def endReg (i : Fin 7) : Fin 32 := ⟨12 + i.val, by omega⟩
private def targetReg (i : Fin 7) : Fin 32 := ⟨19 + i.val, by omega⟩
private def sourcePort (i : Fin 7) : Fin 14 := Fin.natAdd 7 i

private theorem data_source (L : Lengths) (N : ℕ) (shadow table lengthsSource : Word w)
    (source : Fin 7 → Word w) (i : Fin 7) : data L N shadow table lengthsSource source (sourcePort i) = source i := by
  fin_cases i <;> rfl

/-- Read the two live cut lengths, compute cumulative ends and shadow destinations for all
seven fields, and advance the incoming state word. -/
def setup : Ops :=
  [.constant 0 1, .constant 1 3, .publicWord 2 0, .publicWord 3 1, .publicWord 4 2, .publicWord 5 3,
   .publicWord 6 4, .publicWord 7 5, .publicWord 8 6, .constant 9 2, .binary .add 9 8 9, .read 10 8,
   .read 11 9, .copy 12 1, .binary .add 13 12 2, .binary .add 14 13 2, .binary .add 15 14 3,
   .binary .add 16 15 10, .binary .add 17 16 11, .binary .add 18 17 5, .copy 19 6,
   .binary .add 20 19 1, .binary .add 21 20 2, .binary .add 22 21 2, .binary .add 23 22 3,
   .binary .add 24 23 4, .binary .add 25 24 4, .stateWord 27, .binary .add 27 27 0]

private def rowOps (i : Fin 7) : Ops :=
  [.write 7 (endReg i), .binary .add 7 7 0, .publicWord 26 (sourcePort i), .write 7 26,
   .binary .add 7 7 0, .write 7 (targetReg i), .binary .add 7 7 0]

/-- The complete initializer instruction sequence, performing setup before writing the seven
descriptor triples. -/
def ops : Ops := setup ++ (List.finRange 7).flatMap rowOps

/-- Instantiate the descriptor initializer on the supplied lengths and addresses, returning the
advanced state word from register 27. -/
def program (L : Lengths) (N : ℕ) (shadow table lengthsSource : Word w) (source : Fin 7 → Word w) :=
  ((template ops 27).instantiate w (data L N shadow table lengthsSource source)).program

/-- The descriptor for one auxiliary field, recording its exclusive packed end, source address,
and destination in the sparse shadow. -/
def rows (L : Lengths) (N : ℕ) (shadow : Word w) (source : Fin 7 → Word w) (i : Fin 7) : Descriptor w :=
  ⟨(rangeStart L N i.succ : Word w), source i, ((shadow.val + destinationStart L i : ℕ) : Word w)⟩

/-- Write the cumulative end, source base, and destination base of one row, in order. -/
def putRow (table : Word w) (i : Fin 7) (row : Descriptor w) (m : Memory w) : Memory w :=
  let m₁ := writeMemory m (address table i 0) row.endOffset
  let m₂ := writeMemory m₁ (address table i 1) row.sourceBase
  writeMemory m₂ (address table i 2) row.targetBase

/-- The interpreter stores rows in the order of the supplied list. -/
def storeRows (table : Word w) (rows : Fin 7 → Descriptor w) : List (Fin 7) → Memory w → Memory w
  | [], m => m
  | i :: is, m => storeRows table rows is (putRow table i (rows i) m)

theorem address_val (table : Word w) (fit : table.val + 21 ≤ 2^w) (i : Fin 7) (f : Fin 3) :
    (address table i f).val = table.val + (3*i.val + f.val) := by
  have hi := i.isLt
  have hf := f.isLt
  have offsetFit : 3*i.val + f.val < 2^w := by omega
  rw [address, Fin.val_add, Fin.val_natCast, Nat.mod_eq_of_lt offsetFit, Nat.mod_eq_of_lt (by omega)]

private theorem address_eq_iff (table : Word w) (fit : table.val + 21 ≤ 2^w)
    (i j : Fin 7) (f g : Fin 3) :
    (address table i f).val = (address table j g).val ↔ i = j ∧ f = g := by
  rw [address_val table fit, address_val table fit]
  have hf := f.isLt
  have hg := g.isLt
  simp only [Fin.ext_iff]
  omega

private def rowWord (row : Descriptor w) (f : Fin 3) : Word w :=
  if f = 0 then row.endOffset else if f = 1 then row.sourceBase else row.targetBase

private theorem putRow_at (table : Word w) (fit : table.val + 21 ≤ 2^w)
    (i j : Fin 7) (row : Descriptor w) (m : Memory w) (f : Fin 3) :
    putRow table j row m (address table i f).val =
      if i = j then rowWord row f else m (address table i f).val := by
  by_cases h : i = j
  · subst j
    fin_cases f <;> simp (config := {decide := true}) [putRow, writeMemory, rowWord, address_eq_iff table fit]
  · simp [putRow, writeMemory, address_eq_iff table fit, h]

private theorem storeRows_at (table : Word w) (fit : table.val + 21 ≤ 2^w)
    (rows : Fin 7 → Descriptor w) (cells : List (Fin 7)) (m : Memory w) (i : Fin 7) (f : Fin 3) :
    storeRows table rows cells m (address table i f).val =
      if i ∈ cells then rowWord (rows i) f else m (address table i f).val := by
  induction cells generalizing m with
  | nil => simp [storeRows]
  | cons j js ih =>
    rw [storeRows, ih, putRow_at table fit]
    by_cases h : i = j
    · subst j
      simp
    · simp [h]

theorem storeRows_spec (table : Word w) (fit : table.val + 21 ≤ 2^w)
    (rows : Fin 7 → Descriptor w) (m : Memory w) :
    Spec table rows (storeRows table rows (List.finRange 7) m) := by
  constructor <;> intro i <;>
    rw [storeRows_at table fit, ite_eq_left (List.mem_finRange i)] <;> rfl

/-- The sequence of row writes preserves every address outside the table. -/
theorem storeRows_outside (table : Word w) (fit : table.val + 21 ≤ 2^w)
    (rows : Fin 7 → Descriptor w) (cells : List (Fin 7)) (m : Memory w) (a : ℕ)
    (ha : a < table.val ∨ table.val + 21 ≤ a) : storeRows table rows cells m a = m a := by
  have away (i : Fin 7) (f : Fin 3) : a ≠ (address table i f).val := by
    rw [address_val table fit]
    have hi := i.isLt
    have hf := f.isLt
    omega
  induction cells generalizing m with
  | nil => rfl
  | cons i cells ih => simp [storeRows, ih, putRow, writeMemory, away]

private structure Prepared (L : Lengths) (N : ℕ) (shadow state : Word w) (rs : Regs w 32) : Prop where
  one : rs 0 = 1
  next : rs 27 = state + 1
  ends : ∀ i, rs (endReg i) = (rangeStart L N i.succ : Word w)
  targets : ∀ i, rs (targetReg i) = ((shadow.val + destinationStart L i : ℕ) : Word w)

private theorem setup_trace (L : Lengths) (N : ℕ) (shadow table lengthsSource : Word w)
    (source : Fin 7 → Word w) (state : Word w) (m : Memory w)
    (hleft : m lengthsSource.val = (L.leftCut : Word w))
    (hright : m (lengthsSource + 2).val = (L.rightCut : Word w)) :
    ∃ es out, trace (data L N shadow table lengthsSource source) state setup (fun _ => 0) m = some (es,out,m) ∧
      after m es = m ∧ es.length = 29 ∧ countProbes es = 2 ∧ choiceBits es = [] ∧
      out 7 = table ∧ Prepared L N shadow state out := by
  let es : List (Event w) := List.replicate 11 .tick ++ [.read lengthsSource (L.leftCut : Word w),
    .read (lengthsSource+2) (L.rightCut : Word w)] ++ List.replicate 16 .tick
  let regs : Regs w 32 := ![1, 3, (L.index : Word w), (L.advice : Word w), (L.cutCapacity : Word w),
    (N : Word w), shadow, table, lengthsSource, lengthsSource + 2, (L.leftCut : Word w), (L.rightCut : Word w),
    3, 3 + L.index, 3 + 2*(L.index : Word w), 3 + 2*(L.index : Word w) + L.advice,
    3 + 2*(L.index : Word w) + L.advice + L.leftCut,
    3 + 2*(L.index : Word w) + L.advice + L.leftCut + L.rightCut,
    3 + 2*(L.index : Word w) + L.advice + L.leftCut + L.rightCut + N,
    shadow, shadow+3, shadow+3+L.index, shadow+3+2*(L.index : Word w),
    shadow+3+2*(L.index : Word w)+L.advice, shadow+3+2*(L.index : Word w)+L.advice+L.cutCapacity,
    shadow+3+2*(L.index : Word w)+L.advice+2*(L.cutCapacity : Word w), 0, state+1, 0, 0, 0, 0]
  refine ⟨es, regs, ?_, rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl, ?_, ?_⟩⟩
  · simp (config := {decide := true}) [setup, trace, Op.effect, Function.update, data,
      show BinaryOp.add.eval = (· + · : Word w → Word w → Word w) from rfl, hleft, hright, es,
      List.replicate_succ]
    funext i
    fin_cases i <;> simp (config := {decide := true}) [regs, Function.update] <;> ring
  · intro i
    fin_cases i <;> simp [endReg, rangeStart, exteriorBase, regs]
  · intro i
    fin_cases i <;> simp [targetReg, destinationStart, exteriorBase, Header.count, regs] <;> ring

private theorem row_trace (L : Lengths) (N : ℕ) (shadow table lengthsSource : Word w)
    (source : Fin 7 → Word w) (state : Word w) (m : Memory w) (rs : Regs w 32)
    (i : Fin 7) (ready : Prepared L N shadow state rs) (ptr : rs 7 = address table i 0) :
    let mem := putRow table i (rows L N shadow source i) m
    ∃ es out, trace (data L N shadow table lengthsSource source) state (rowOps i) rs m = some (es,out,mem) ∧
      after m es = mem ∧ es.length = 7 ∧ countProbes es = 3 ∧ choiceBits es = [] ∧
      out 7 = table + ((3*(i.val+1) : ℕ) : Word w) ∧ Prepared L N shadow state out := by
  dsimp only
  let row := rows L N shadow source i
  let es : List (Event w) := [.write (address table i 0) row.endOffset, .tick, .tick,
    .write (address table i 1) row.sourceBase, .tick, .write (address table i 2) row.targetBase, .tick]
  let out := Function.update (Function.update (Function.update (Function.update rs 7 (rs 7+1))
    26 (source i)) 7 (rs 7+1+1)) 7 (rs 7+1+1+1)
  have a₁ : rs 7 + 1 = address table i 1 := by simp [ptr,address,add_assoc]
  have a₂ : rs 7 + 1 + 1 = address table i 2 := by simp [ptr,address]; ring
  have ne₁ (j : Fin 7) : targetReg j ≠ 7 := by simp [targetReg, Fin.ext_iff]; omega
  have ne₂ (j : Fin 7) : targetReg j ≠ 26 := by simp [targetReg, Fin.ext_iff]; omega
  have ne₃ (j : Fin 7) : endReg j ≠ 7 := by simp [endReg, Fin.ext_iff]; omega
  have ne₄ (j : Fin 7) : endReg j ≠ 26 := by simp [endReg, Fin.ext_iff]; omega
  refine ⟨es,out,?_,rfl,rfl,rfl,rfl,?_,?_⟩
  · simp (config := {decide := true}) [rowOps, trace, Op.effect,
      show BinaryOp.add.eval = (· + · : Word w → Word w → Word w) from rfl, out, es, row,
      putRow, rows, ready.one, ready.ends, ready.targets, data_source, ne₁, ne₂,
      Function.update_of_ne, ← ptr, ← a₁, ← a₂]
  · change rs 7+1+1+1 = _
    rw [ptr]; simp [address]; ring
  · refine ⟨ready.one, ready.next, ?_, ?_⟩
    · intro j
      simp [out, ne₃, ne₄, ready.ends]
    · intro j
      simp [out, ne₁, ne₂, ready.targets]

private theorem count_append (es fs : List (Event w)) :
    countProbes (es ++ fs) = countProbes es + countProbes fs := by
  induction es with
  | nil => simp [countProbes]
  | cons e es ih => cases e <;> simp [countProbes, ih, Nat.add_assoc]

private theorem trace_cells (L : Lengths) (N : ℕ) (shadow table lengthsSource : Word w)
    (source : Fin 7 → Word w) (state : Word w) (cells : List (Fin 7)) (start : ℕ)
    (aligned : cells.map Fin.val = List.range' start cells.length) (m : Memory w) (rs : Regs w 32)
    (ready : Prepared L N shadow state rs) (ptr : rs 7 = table + ((3*start : ℕ) : Word w)) :
    let mem := storeRows table (rows L N shadow source) cells m
    ∃ es out, trace (data L N shadow table lengthsSource source) state (cells.flatMap rowOps) rs m = some (es,out,mem) ∧
      after m es = mem ∧ es.length = 7*cells.length ∧ countProbes es = 3*cells.length ∧
      choiceBits es = [] ∧ out 27 = state+1 := by
  dsimp only
  induction cells generalizing start m rs with
  | nil => exact ⟨[],rs,rfl,rfl,rfl,rfl,rfl,ready.next⟩
  | cons i cells ih =>
    simp only [List.map_cons, List.length_cons, List.range'_succ, List.cons.injEq] at aligned
    obtain ⟨rfl, aligned⟩ := aligned
    obtain ⟨es, tmp, he, hm, hl, hp, hb, hptr, hr⟩ :=
      row_trace L N shadow table lengthsSource source state m rs i ready (by simpa [address] using ptr)
    obtain ⟨fs, out, hf, hn, hfLen, hfProbe, hfBits, hnext⟩ := ih _ aligned (putRow table i (rows L N shadow source i) m) tmp hr hptr
    refine ⟨es ++ fs, out, ?_, ?_, ?_, ?_, ?_, hnext⟩
    · rw [List.flatMap_cons, trace_append, he]
      simp [hf,storeRows]
    · rw [after, List.foldl_append, show es.foldl update m = _ from hm]
      exact hn
    · simp only [List.length_append, hl, hfLen, List.length_cons]; omega
    · simp only [count_append, hp, hfProbe, List.length_cons]; omega
    · simp [Flow.choiceBits_append,hb,hfBits]

/-- Construct the descriptor table from the public layout and the two exterior lengths
already stored in scratch memory. A single native call reads two words and writes twenty-one. -/
theorem init_native (L : Lengths) (N : ℕ) (shadow table lengthsSource : Word w) (source : Fin 7 → Word w)
    (state : Word w) (m : Memory w) (fit : table.val + 21 ≤ 2^w)
    (hleft : m lengthsSource.val = (L.leftCut : Word w)) (hright : m (lengthsSource+2).val = (L.rightCut : Word w)) :
    let P := program L N shadow table lengthsSource source
    ∃ es, execute P 79 (P.start state) m [] = some ⟨es,some (state+1)⟩ ∧
      Spec table (rows L N shadow source) (after m es) ∧
      (∀ a, a < table.val ∨ table.val + 21 ≤ a → after m es a = m a) ∧
      es.length = 78 ∧ countProbes es = 23 ∧ choiceBits es = [] := by
  dsimp only
  obtain ⟨es, rs, he, hm, hl, hp, hb, ptr, ready⟩ :=
    setup_trace L N shadow table lengthsSource source state m hleft hright
  obtain ⟨fs, out, hf, hn, hflen, hfprobe, hfbits, hret⟩ := trace_cells L N shadow table lengthsSource source
    state (List.finRange 7) 0 (by decide) m rs ready (by simpa using ptr)
  have hafter : after m (es ++ fs) = storeRows table (rows L N shadow source) (List.finRange 7) m := by
    rw [after, List.foldl_append, show es.foldl update m = m from hm]
    exact hn
  refine ⟨es ++ fs, ?_, hafter ▸ storeRows_spec table fit _ m, ?_, ?_, ?_, ?_⟩
  · let pub := data L N shadow table lengthsSource source
    change execute ((template ops 27).instantiate w pub).program (1+ops.length) ⟨_,state,fun _ => 0,fun _ => 0⟩ m [] = _
    rw [execute_template, run_eq_trace, ops, trace_append, he]
    simp [pub, hf, hret]
  · intro a ha
    rw [hafter]
    exact storeRows_outside table fit _ _ m a ha
  · simp [hl,hflen]
  · simp [count_append,hp,hfprobe]
  · simp [Flow.choiceBits_append,hb,hfbits]

end LiveAuxiliaryDescriptorInit

end VPVNP
end Computability
end OAI

import OAI.Computability.VPVNP.CompressorRecordSlices
import OAI.Computability.VPVNP.RAMRecords
import OAI.Computability.VPVNP.PrimedStackRAMCode

/-!
# Burst RAM interval intersection

A fixed instruction table intersects a candidate pair of fields from Appendix E.
The persistent word points to a frame with four input words and three output
cells. The table reads the two starts and widths. A nonempty intersection writes
two offsets and a length. An empty intersection returns zero after the four reads.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.SliceRAM

open BurstRAM BurstRAM.PrivateRAM Compression.PackingData

/-- Labels 17–28 load the frame. Labels 0–16 select the larger start and
smaller end and skip all three writes when the intersection is empty. -/
def pairTemplate : Template 29 14 0 where
  literalWidth := 1
  entry := 17
  code pc := match pc.val with
    | 0 => .binary .add 4 0 1 1
    | 1 => .binary .add 5 2 3 2
    | 2 => .jumpLt 0 2 3 4
    | 3 => .copy 6 2 5
    | 4 => .copy 6 0 5
    | 5 => .jumpLt 4 5 6 7
    | 6 => .copy 7 4 8
    | 7 => .copy 7 5 8
    | 8 => .jumpLt 6 7 9 16
    | 9 => .binary .sub 8 6 0 10
    | 10 => .binary .sub 9 6 2 11
    | 11 => .binary .sub 10 7 6 12
    | 12 => .writeExternal 11 8 13
    | 13 => .writeExternal 12 9 14
    | 14 => .writeExternal 13 10 15
    | 15 => .returnState 10
    | 16 => .constant 10 0 15
    | 17 => .stateWord 11 18
    | 18 => .constant 6 1 19
    | 19 => .readExternal 0 11 20
    | 20 => .binary .add 12 11 6 21
    | 21 => .readExternal 1 12 22
    | 22 => .binary .add 13 12 6 23
    | 23 => .readExternal 2 13 24
    | 24 => .binary .add 11 13 6 25
    | 25 => .readExternal 3 11 26
    | 26 => .binary .add 11 11 6 27
    | 27 => .binary .add 12 11 6 28
    | _ => .binary .add 13 12 6 0

variable {w : ℕ}

private def lower (s t : Word w) := if s < t then t else s
private def upper (s t : Word w) := if s < t then s else t

private def written (rs : Fin 14 → Word w) (lo hi : Word w) : Report w :=
  ⟨List.replicate 10 .tick ++
    [.write (rs 11) (lo - rs 0), .write (rs 12) (lo - rs 2), .write (rs 13) (hi - lo)],
    some (hi - lo)⟩

private def skipped (w : ℕ) : Report w := ⟨List.replicate 8 .tick, some 0⟩

private theorem execute_words (pub : Fin 0 → Word w) (state : Word w) (rs : Fin 14 → Word w)
    (priv : Word w → Word w) (mem : Memory w) :
    let M := pairTemplate.instantiate w pub
    let lo := lower (rs 0) (rs 2)
    let hi := upper (rs 0 + rs 1) (rs 2 + rs 3)
    execute M.program 14 ⟨0, state, rs, priv⟩ mem [] =
      some (if lo < hi then written rs lo hi else skipped w) := by
  dsimp only
  by_cases hl : rs 0 < rs 2 <;> by_cases hh : rs 0 + rs 1 < rs 2 + rs 3 <;>
    simp only [lower, upper, hl, hh, ↓reduceIte]
  all_goals
    split <;> rename_i hc <;>
    simp (config := { decide := true }) [pairTemplate, Template.instantiate, Machine.program,
      execute, Instr.resize, Instr.run, Config.put, BinaryOp.eval, Function.update,
      hl, hh, hc, written, skipped, Report.prepend]

private def wordNat (n : ℕ) : Word w := Fin.ofNat _ n

private theorem word_val (x : Word w) : wordNat x.val = x :=
  Fin.ext (Nat.mod_eq_of_lt x.isLt)

/-- The native events prescribed by the descriptor. Source and target offsets
are written only when the interval contains a bit. -/
def resultReport (rs : Fin 14 → Word w) (slice : CopySlice) : Report w :=
  if slice.length = 0 then skipped w else
    ⟨List.replicate 10 .tick ++
      [.write (rs 11) (wordNat slice.sourceOffset), .write (rs 12) (wordNat slice.targetOffset),
        .write (rs 13) (wordNat slice.length)], some (wordNat slice.length)⟩

/-- From label zero, the table executes the pair test with fields already loaded. -/
theorem execute_slice (pub : Fin 0 → Word w) (state : Word w) (rs : Fin 14 → Word w)
    (priv : Word w → Word w) (mem : Memory w)
    (hs : (rs 0).val + (rs 1).val < 2^w) (ht : (rs 2).val + (rs 3).val < 2^w) :
    let M := pairTemplate.instantiate w pub
    let slice := copySlice (rs 0).val (rs 1).val (rs 2).val (rs 3).val
    execute M.program 14 ⟨0,state,rs,priv⟩ mem [] = some (resultReport rs slice) := by
  dsimp only
  rw [execute_words]
  let lo := lower (rs 0) (rs 2)
  let hi := upper (rs 0 + rs 1) (rs 2 + rs 3)
  let slice := copySlice (rs 0).val (rs 1).val (rs 2).val (rs 3).val
  have hl : lo.val = max (rs 0).val (rs 2).val := by
    by_cases h : rs 0 < rs 2
    · simp [lo, lower, h, max_eq_right (Fin.le_iff_val_le_val.mp h.le)]
    · change (if rs 0 < rs 2 then rs 2 else rs 0).val = _
      rw [ite_eq_right h, max_eq_left (Fin.le_iff_val_le_val.mp (le_of_not_gt h))]
  have he₁ : (rs 0 + rs 1).val = (rs 0).val + (rs 1).val := by
    rw [Fin.val_add, Nat.mod_eq_of_lt hs]
  have he₂ : (rs 2 + rs 3).val = (rs 2).val + (rs 3).val := by
    rw [Fin.val_add, Nat.mod_eq_of_lt ht]
  have hu : hi.val = min ((rs 0).val + (rs 1).val) ((rs 2).val + (rs 3).val) := by
    rw [← he₁, ← he₂]
    by_cases h : rs 0 + rs 1 < rs 2 + rs 3
    · simp [hi, upper, h, min_eq_left (Fin.le_iff_val_le_val.mp h.le)]
    · simp [hi, upper, h, min_eq_right (Fin.le_iff_val_le_val.mp (le_of_not_gt h))]
  have hlen : slice.length = hi.val - lo.val := by simp [slice, copySlice, hl, hu]
  change some (if lo < hi then written rs lo hi else skipped w) = some (resultReport rs slice)
  by_cases h : lo < hi
  · have hpos : slice.length ≠ 0 := by rw [hlen]; have := Fin.lt_def.mp h; omega
    have ho₁ : lo - rs 0 = wordNat slice.sourceOffset := by
      have hle : rs 0 ≤ lo := Fin.le_iff_val_le_val.mpr (hl ▸ le_max_left ..)
      rw [← word_val (lo - rs 0), Fin.sub_val_of_le hle, hl]
      rfl
    have ho₂ : lo - rs 2 = wordNat slice.targetOffset := by
      have hle : rs 2 ≤ lo := Fin.le_iff_val_le_val.mpr (hl ▸ le_max_right ..)
      rw [← word_val (lo - rs 2), Fin.sub_val_of_le hle, hl]
      rfl
    have hz : hi - lo = wordNat slice.length := by
      rw [← word_val (hi-lo), Fin.sub_val_of_le h.le, hlen]
    simp [h, resultReport, hpos, written, ho₁, ho₂, hz]
  · have hzero : slice.length = 0 := by rw [hlen]; exact Nat.sub_eq_zero_of_le (le_of_not_gt h)
    simp [h, resultReport, hzero]

/-- Three probes and thirteen nonterminal instructions suffice for a nonempty
copy. A disjoint pair takes eight nonterminal instructions and zero probes. -/
theorem resultReport_cost (rs : Fin 14 → Word w) (slice : CopySlice) :
    (resultReport rs slice).probes = (if slice.length = 0 then 0 else 3) ∧
      (resultReport rs slice).events.length = (if slice.length = 0 then 8 else 13) := by
  by_cases h : slice.length = 0 <;> simp only [resultReport, h, ↓reduceIte] <;> exact ⟨rfl,rfl⟩

/-- Consecutive cells of a seven-word frame, with the burst machine's modular addresses. -/
def frameAddress (base : Word w) : ℕ → Word w
  | 0 => base
  | i + 1 => frameAddress base i + 1

/-- Every cell of a frame fitting the address space has its ordinary consecutive address. -/
theorem frameAddress_val (base : Word w) (i : ℕ) (h : base.val + i < 2^w) :
    (frameAddress base i).val = base.val + i := by
  induction i with
  | zero => simp [frameAddress]
  | succ i ih =>
    have h1 : (1 : Word w).val = 1 := by
      rw [Fin.val_one', Nat.mod_eq_of_lt (show 1 < 2^w by omega)]
    rw [frameAddress, Fin.val_add, ih (by omega), h1, Nat.mod_eq_of_lt (by omega)]
    omega

private def frameRegs (base : Word w) (mem : Memory w) : Fin 14 → Word w :=
  ![mem base.val, mem (frameAddress base 1).val, mem (frameAddress base 2).val,
    mem (frameAddress base 3).val, 0, 0, 1, 0, 0, 0, 0, frameAddress base 4,
    frameAddress base 5, frameAddress base 6]

private def frameEvents (base : Word w) (mem : Memory w) : List (Event w) :=
  [.tick, .tick, .read base (mem base.val), .tick,
    .read (frameAddress base 1) (mem (frameAddress base 1).val), .tick,
    .read (frameAddress base 2) (mem (frameAddress base 2).val), .tick,
    .read (frameAddress base 3) (mem (frameAddress base 3).val), .tick, .tick, .tick]

private theorem execute_frame_prefix (pub : Fin 0 → Word w) (base : Word w) (mem : Memory w)
    (fuel : ℕ) :
    let M := pairTemplate.instantiate w pub
    execute M.program (fuel + 12) (M.program.start base) mem [] =
      (execute M.program fuel ⟨0, base, frameRegs base mem, fun _ => 0⟩ mem []).map
        (fun r => ⟨frameEvents base mem ++ r.events, r.result⟩) := by
  simp (config := { decide := true }) [execute, Machine.program, pairTemplate, Template.instantiate,
    Instr.run, Instr.resize, Config.put, BinaryOp.eval, Report.prepend, Function.comp_def,
    frameAddress, frameEvents]
  congr 4
  funext i
  fin_cases i <;> rfl

/-- The four input words of a candidate test in a caller's memory. -/
def frameHolds (base : Word w) (mem : Memory w) (p : Field × Field) : Prop :=
  (mem base.val).val = p.1.start ∧
  (mem (frameAddress base 1).val).val = p.1.width ∧
  (mem (frameAddress base 2).val).val = p.2.start ∧
  (mem (frameAddress base 3).val).val = p.2.width

/-- Exact report for the whole candidate call, including its frame reads. -/
def frameReport (base : Word w) (mem : Memory w) (p : Field × Field) : Report w :=
  let r := resultReport (frameRegs base mem) (copySlice p.1.start p.1.width p.2.start p.2.width)
  ⟨frameEvents base mem ++ r.events, r.result⟩

/-- Fresh-call execution for every field pair of the source-major scan. The
two bounds on total widths suffice for all its endpoint additions. -/
theorem execute_candidate (pub : Fin 0 → Word w) (base : Word w) (mem : Memory w)
    {old new : List ℕ} (p : Field × Field) (hmem : frameHolds base mem p)
    (hp : p ∈ candidates old new) (hs : old.sum < 2^w) (ht : new.sum < 2^w) :
    let M := pairTemplate.instantiate w pub
    execute M.program 26 (M.program.start base) mem [] = some (frameReport base mem p) := by
  obtain ⟨ho,hn⟩ := List.mem_product.mp hp
  have hse := (fieldsFrom_bounds ho).2.2.2
  have hte := (fieldsFrom_bounds hn).2.2.2
  obtain ⟨h₀,h₁,h₂,h₃⟩ := hmem
  dsimp only
  rw [execute_frame_prefix pub base mem 14, execute_slice]
  · simp [frameReport, frameRegs, h₀, h₁, h₂, h₃]
  · change (mem base.val).val + (mem (frameAddress base 1).val).val < 2^w
    omega
  · change (mem (frameAddress base 2).val).val + (mem (frameAddress base 3).val).val < 2^w
    omega

/-- The frame contributes four reads and twelve instructions. The final
return costs one instruction in both cases. -/
theorem frameReport_cost (base : Word w) (mem : Memory w) (p : Field × Field) :
    let emitted := (intersectFields p).isSome
    (frameReport base mem p).probes = 4 + (if emitted then 3 else 0) ∧
      (frameReport base mem p).events.length + 1 = 21 + (if emitted then 5 else 0) := by
  by_cases h : (copySlice p.1.start p.1.width p.2.start p.2.width).length = 0 <;>
    simp only [intersectFields, frameReport, resultReport, h, ↓reduceIte] <;> exact ⟨rfl,rfl⟩

/-- Replay gives exactly the three specified writes for a nonempty interval
and preserves memory on the empty branch. -/
theorem frameReport_after (base : Word w) (mem : Memory w) (p : Field × Field) :
    let s := copySlice p.1.start p.1.width p.2.start p.2.width
    after mem (frameReport base mem p).events = if s.length = 0 then mem else
      writeMemory (writeMemory (writeMemory mem (frameAddress base 4) (Fin.ofNat _ s.sourceOffset))
        (frameAddress base 5) (Fin.ofNat _ s.targetOffset)) (frameAddress base 6) (Fin.ofNat _ s.length) := by
  dsimp only
  by_cases h : (copySlice p.1.start p.1.width p.2.start p.2.width).length = 0 <;>
    simp only [frameReport, resultReport, h, ↓reduceIte] <;> rfl

private theorem sum_frame_cost (base : Field × Field → Word w) (mem : Field × Field → Memory w)
    (pairs : List (Field × Field)) :
    let reports := pairs.map fun p => frameReport (base p) (mem p) p
    (reports.map Report.probes).sum = 4 * pairs.length + 3 * (pairs.filterMap intersectFields).length ∧
      (reports.map (fun r => r.events.length + 1)).sum =
        21 * pairs.length + 5 * (pairs.filterMap intersectFields).length := by
  induction pairs with
  | nil => simp
  | cons p pairs ih =>
    obtain ⟨hprobes,hsteps⟩ := frameReport_cost (base p) (mem p) p
    cases h : intersectFields p <;>
      simp only [List.map_cons, List.sum_cons, List.filterMap_cons, List.length_cons, h,
        Option.isSome_none, Option.isSome_some, Bool.false_eq_true, ↓reduceIte] at *
    all_goals omega

/-- Exact cost of all candidate-test calls. Memories can differ from one
call to the next. Each report is native under the frame invariant of
`execute_candidate`. The cost depends only on field and record counts. -/
theorem scan_cost (old new : List ℕ) (base : Field × Field → Word w)
    (mem : Field × Field → Memory w) :
    let reports := (candidates old new).map fun p => frameReport (base p) (mem p) p
    (reports.map Report.probes).sum = 4 * (old.length * new.length) + 3 * (copyRecords old new).length ∧
      (reports.map (fun r => r.events.length + 1)).sum =
        21 * (old.length * new.length) + 5 * (copyRecords old new).length := by
  simpa only [candidates_length, copyRecords] using sum_frame_cost base mem (candidates old new)

section PrefixScan

open PrimedStackRAM

/-- One step of `fieldsFrom` with the width in external memory. Registers
0 and 1 carry the index and prefix sum. Register 2 supplies the width address
and registers 3–5 supply the index, start and width output addresses. -/
def fieldOps : List (Op 8 0) :=
  [.read 6 2, .write 3 0, .write 4 1, .write 5 6, .binary .add 1 1 6,
    .constant 7 1, .binary .add 0 0 7]

/-- The prefix scan reads one width, writes one indexed descriptor and
advances both running totals. -/
theorem fieldOps_trace (pub : Fin 0 → Word w) (state : Word w) (rs : Regs w 8) (mem : Memory w) :
    let width := mem (rs 2).val
    let es := [.read (rs 2) width, .write (rs 3) (rs 0), .write (rs 4) (rs 1),
      .write (rs 5) width, .tick, .tick, .tick]
    ∃ rs', trace pub state fieldOps rs mem = some (es, rs', after mem es) ∧
      rs' 0 = rs 0 + 1 ∧ rs' 1 = rs 1 + width := by
  simp (config := { decide := true }) [fieldOps, trace, Op.effect, BinaryOp.eval, Function.update,
    after, update]
  rfl

/-- Numeric field and next prefix computed by the straight-line native code,
under the usual index and address-width bounds. -/
theorem fieldOps_native (pub : Fin 0 → Word w) (state : Word w) (rs : Regs w 8)
    (priv : Word w → Word w) (mem : Memory w) (hi : (rs 0).val + 1 < 2^w)
    (hw : (rs 1).val + (mem (rs 2).val).val < 2^w) :
    let M := (template fieldOps 1).instantiate w pub
    let width := mem (rs 2).val
    ∃ es post, trace pub state fieldOps rs mem = some (es, post, after mem es) ∧
      execute M.program 8 ⟨M.entry,state,rs,priv⟩ mem [] = some ⟨es, some (post 1)⟩ ∧
      es = [.read (rs 2) width, .write (rs 3) (rs 0), .write (rs 4) (rs 1),
        .write (rs 5) width, .tick, .tick, .tick] ∧
      (post 0).val = (rs 0).val + 1 ∧ (post 1).val = (rs 1).val + width.val ∧
      countProbes es = 4 ∧ es.length + 1 = 8 := by
  obtain ⟨rs',h,hn,hp⟩ := fieldOps_trace pub state rs mem
  refine ⟨_,rs',h,?_,rfl,?_,?_,rfl,rfl⟩
  · change execute ((template fieldOps 1).instantiate w pub).program (1 + fieldOps.length)
      _ mem [] = _
    rw [execute_template, run_eq_trace, h]
    simp
  · have h1 : (1 : Word w).val = 1 := by
      rw [Fin.val_one', Nat.mod_eq_of_lt (show 1 < 2^w by omega)]
    rw [hn, Fin.val_add, h1, Nat.mod_eq_of_lt hi]
  · rw [hp, Fin.val_add, Nat.mod_eq_of_lt hw]

/-- The two prefix scans plus all interval tests use a width-independent
number of word instructions and probes. This accounts for the prefix steps
and the candidate calls with their input frames in place. -/
theorem scan_bounds (old new : List ℕ) (base : Field × Field → Word w)
    (mem : Field × Field → Memory w) :
    let reports := (candidates old new).map fun p => frameReport (base p) (mem p) p
    let fields := old.length + new.length
    let pairs := old.length * new.length
    4 * fields + (reports.map Report.probes).sum ≤ 4 * fields + 7 * pairs ∧
      8 * fields + (reports.map fun r => r.events.length + 1).sum ≤ 8 * fields + 26 * pairs := by
  have h := scan_cost old new base mem
  have hsize := copyRecords_length_le old new
  dsimp only at *
  omega

end PrefixScan

end CompressorRecords.SliceRAM

end VPVNP
end Computability
end OAI

import OAI.Computability.VPVNP.LiveHeaderCutInput
import OAI.Computability.VPVNP.LiveHeaderBoundedRun

/-!
# Copying the distributed live advice

Processor `j` holds advice bit `j` in slot one of its physical header. The
native scan reads each occupied header and writes its bit as a separate word
in the public advice array. The scratch array starts beyond the processor
sites, so later stages can still read all four fields at every site.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveHeader

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM ChainAssignments CutSchedule
open scoped Fin.CommRing

variable {w d a h Δ : ℕ}

/-- The native table for the advice stage. -/
abbrev adviceTable := template (copyCell 1) 7

/-- Advice readback, preservation of the packed site headers, and the frame
for every word outside the allocated advice array. -/
structure AdviceImage (hw : 4 ≤ w) (advice : Bits a) (cuts : AllCuts h Δ) (g : Fin (2^(h+1)))
    (base : ℕ) (original out : Memory w) : Prop where
  copied : ∀ i : Fin a, out (base+i.val) = PrimedInputRAM.encodeBit w (advice i)
  headers : SiteHeaders d hw advice cuts g out
  frame : ∀ addr, addr < base ∨ base+a ≤ addr → out addr = original addr

private theorem adviceImage_of_copy {hw : 4 ≤ w} {advice : Bits a} {cuts : AllCuts h Δ}
    {g : Fin (2^(h+1))} {m out : Memory w} {base : ℕ} (headers : SiteHeaders d hw advice cuts g m)
    (sites : a ≤ 2^d) (scratch : 2^d ≤ base) (copy : FieldCopy m 1 0 base a out) :
    AdviceImage (d := d) hw advice cuts g base m out := by
  refine ⟨?_, ?_, copy.frame⟩
  · intro i
    let v : Fin (2^d) := ⟨i.val, i.isLt.trans_le sites⟩
    have hb := headers.bit v 1
    change (m i.val).val.testBit (1 : Fin 4).val = distributedBit advice i.val at hb
    simpa only [Nat.zero_add, hb, distributedBit, dite_eq_left i.isLt] using copy.copied i.val i.isLt
  · intro v
    rw [copy.frame v.val (Or.inl (v.isLt.trans_le scratch)), headers v]

private theorem advice_step (hw : 4 ≤ w) (pub : Fin 2 → Word w) (zero : pub 0 = 0)
    (m : Memory w) (j len : ℕ) (hj : j < len) (disjoint : len ≤ (pub 1).val)
    (fit : (pub 1).val + len ≤ 2^w) (mem : Memory w) (inv : FieldCopy m 1 0 (pub 1).val j mem) :
    let P := (adviceTable.instantiate w pub).program
    ∃ es, execute P 13 (P.start (j : Word w)) mem [] = some ⟨es, some ((j+1 : ℕ) : Word w)⟩ ∧
      FieldCopy m 1 0 (pub 1).val (j+1) (after mem es) ∧ countProbes es ≤ 2 := by
  have hjv : (j : Word w).val = j := Fin.val_cast_of_lt (by omega)
  have dst : (pub 1 + (j : Word w)).val = (pub 1).val+j := by
    rw [Fin.val_add, hjv, Nat.mod_eq_of_lt (by omega)]
  have hread := inv.frame j (Or.inl (by omega))
  obtain ⟨es, rs, ht, hr, _, hp, _⟩ := copyCell_trace hw 1 pub (j : Word w) (fun _ => 0) mem
  refine ⟨es, ?_, ?_, hp.le⟩
  · change execute ((template (copyCell 1) 7).instantiate w pub).program (1+(copyCell 1).length)
      ⟨_,(j : Word w),fun _ => 0,fun _ => 0⟩ mem [] = _
    rw [execute_template, run_eq_trace, ht]
    simp [hr]
  · rw [trace_after ht, zero, sub_zero, hjv, hread]
    constructor
    · intro i hi
      by_cases he : i = j
      · simp [writeMemory, dst, he]
      · simpa [writeMemory, dst, he] using inv.copied i (by omega)
    · intro addr outside
      have hn : addr ≠ (pub 1).val+j := by omega
      simp [writeMemory, dst, hn, inv.frame addr (by omega)]

/-- Execute all occupied advice cells starting with any memory that retains
the physical headers. Zero-length advice gives an empty scan. -/
theorem physical_advice_scan_native {hw : 4 ≤ w} {advice : Bits a} {cuts : AllCuts h Δ}
    {g : Fin (2^(h+1))} {m : Memory w} (headers : SiteHeaders d hw advice cuts g m)
    (pub : Fin 2 → Word w) (zero : pub 0 = 0) (sites : a ≤ 2^d) (scratch : 2^d ≤ (pub 1).val)
    (fit : (pub 1).val+a ≤ 2^w) :
    let P := (adviceTable.instantiate w pub).program
    ∃ rs, runSegment P 13 (some 0) m (List.replicate a []) = some rs ∧
      endState (some 0) rs = some (a : Word w) ∧ rs.length = a ∧
      (∀ rep ∈ rs, countProbes rep.events ≤ 2) ∧
      AdviceImage (d := d) hw advice cuts g (pub 1).val m (after m (eventLog rs)) := by
  obtain ⟨rs, run, last, copy, len, probes⟩ := run_cursor_segment (adviceTable.instantiate w pub).program 13 a 2
    (FieldCopy m 1 0 (pub 1).val) m (FieldCopy.initial ..)
    (fun i hi => advice_step hw pub zero m i a hi (sites.trans scratch) fit)
  exact ⟨rs, run, last, len, probes, adviceImage_of_copy headers sites scratch copy⟩

/-- The bounded advice table executes one active call per bit and closes
with a zero-probe accepting call. Its final memory contains the same advice
image, including when the advice array is empty. -/
theorem physical_advice_bounded_native {hw : 4 ≤ w} {advice : Bits a} {cuts : AllCuts h Δ}
    {g : Fin (2^(h+1))} {m : Memory w} (headers : SiteHeaders d hw advice cuts g m)
    (pub : Fin 2 → Word w) (zero : pub 0 = 0) (sites : a ≤ 2^d) (scratch : 2^d ≤ (pub 1).val)
    (fit : (pub 1).val+a ≤ 2^w) :
    let P := (LiveHeaderBounded.machine adviceTable pub (a : Word w)).program
    ∃ rs, runSegment P 16 (some 0) m (List.replicate (a+1) []) = some rs ∧
      endState (some 0) rs = none ∧ rs.length = a+1 ∧
      (∀ rep ∈ rs, countProbes rep.events ≤ 2) ∧
      AdviceImage (d := d) hw advice cuts g (pub 1).val m (after m (eventLog rs)) := by
  let P := (LiveHeaderBounded.machine adviceTable pub (a : Word w)).program
  have apos := Nat.two_pow_pos d
  have ha : (a : Word w).val = a := Fin.val_cast_of_lt (by omega)
  obtain ⟨rs, run, last, copy, len, probes⟩ := run_cursor_segment P 16 a 2 (FieldCopy m 1 0 (pub 1).val) m
    (FieldCopy.initial ..) (by
      intro j hj mem inv
      have hjv : (j : Word w).val = j := Fin.val_cast_of_lt (by omega)
      have hlt : (j : Word w) < (a : Word w) := Fin.lt_def.mpr (by rwa [hjv, ha])
      obtain ⟨es, he, hnext, hp⟩ := advice_step hw pub zero m j a hj (sites.trans scratch) fit mem inv
      have active := LiveHeaderBounded.execute_active adviceTable pub (a : Word w) 13 (j : Word w) hlt mem []
      dsimp only at active
      rw [he] at active
      exact ⟨.tick :: .tick :: .tick :: es, active, hnext, hp⟩)
  let closed := LiveHeaderBounded.closedReport w
  have halt := LiveHeaderBounded.execute_closed adviceTable pub (a : Word w) 12 (a : Word w) le_rfl
    (after m (eventLog rs)) []
  dsimp only at halt
  refine ⟨rs ++ [closed], ?_, ?_, by simp [len], ?_, ?_⟩
  · rw [List.replicate_succ', PrimedSchedule.runSegment_append, run]
    simp only [Option.bind_some, last, runSegment]
    rw [halt]
    rfl
  · rw [endState_append]
    rfl
  · intro rep hrep
    rcases List.mem_append.mp hrep with h | h
    · exact probes rep h
    · obtain rfl := List.mem_singleton.mp h
      exact Nat.zero_le _
  · have he : after m (eventLog (rs ++ [closed])) = after m (eventLog rs) := by
      simp only [eventLog, List.flatMap_append, List.flatMap_singleton, after, List.foldl_append]
      rfl
    rw [he]
    exact adviceImage_of_copy headers sites scratch copy

end LiveHeader

end VPVNP
end Computability
end OAI

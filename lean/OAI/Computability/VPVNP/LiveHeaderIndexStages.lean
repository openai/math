import OAI.Computability.VPVNP.LiveHeaderIndexInput
import OAI.Computability.VPVNP.LiveHeaderProtectedCore
import OAI.Computability.VPVNP.LiveHeaderCursorFrame

/-!
# The initial index stage of the physical live-header program

The public row supplies the index array, its two summary cells and the scan
length. The actual distributed headers supply the one-based group number.
The closing call accepts and hands its memory to the advice stage.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveHeaderProgram

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM ChainAssignments LiveHeaderSchedule LiveHeader
open scoped Fin.CommRing

variable {w d : ℕ}

/-- The burst table for copying one distributed group-index bit and updating its summary. -/
abbrev indexTable := template indexCell 11

/-- The index worker's three public addresses for the unpacked digits, highest set position,
and population count. -/
def indexWords (w : ℕ) (s : Sizes) (base : ℕ) : Fin 3 → Word w :=
  ![Fin.ofNat _ (indexBase base), Fin.ofNat _ (highAddr s base), Fin.ofNat _ (populationAddr s base)]

theorem index_row (w : ℕ) (s : Sizes) (base : ℕ) :
    rowData w s base .index ∘ includeFin (by decide : 3+1 ≤ 17) =
      LiveHeaderBounded.publicData (indexWords w s base) (Fin.ofNat _ (s.h+2)) := by
  funext j
  fin_cases j <;> rfl

/-- Every successful index-cell call increments the cursor and leaves the
tag unchanged in its real external memory. -/
theorem index_step (hw : 4 ≤ w) (pub : Fin 3 → Word w) (bound : ℕ) (addr : Word w)
    (ha : (pub 0).val + bound ≤ (pub 1).val) (hb : (pub 1).val < (pub 2).val) (htag : addr.val < (pub 0).val)
    (i : ℕ) (hi : i < bound) (m : Memory w) (bits : List Bool) (rep : Report w) {fuel : ℕ}
    (h : execute (indexTable.instantiate w pub).program fuel
      ((indexTable.instantiate w pub).program.start (i : Word w)) m bits = some rep) :
    rep.result = some ((i+1 : ℕ) : Word w) ∧ after m rep.events addr.val = m addr.val := by
  obtain ⟨es, rs', ht, hresult, _, _, _⟩ := indexCell_trace hw pub (i : Word w) (fun _ => 0) m
  have he : execute (indexTable.instantiate w pub).program 22
      ((indexTable.instantiate w pub).program.start (i : Word w)) m [] = some ⟨es, some ((i+1 : ℕ) : Word w)⟩ := by
    change execute ((template indexCell 11).instantiate w pub).program (1+indexCell.length) ⟨_,(i : Word w),fun _ => 0,fun _ => 0⟩ _ [] = _
    rw [execute_template, run_eq_trace, ht]
    simp [hresult]
  obtain ⟨_, rfl⟩ := execute_empty_forces_anyFuel he h
  refine ⟨rfl, ?_⟩
  change after m es addr.val = m addr.val
  rw [trace_after ht]
  have hc := (pub 2).isLt
  have hiv : (i : Word w).val = i := Fin.val_cast_of_lt (by omega)
  have hd : (pub 0 + (i : Word w)).val = (pub 0).val+i := by
    rw [Fin.val_add, hiv, Nat.mod_eq_of_lt (by omega)]
  simp [indexUpdate,writeMemory,hd,show addr.val ≠ (pub 2).val by omega,
    show addr.val ≠ (pub 1).val by omega,show addr.val ≠ (pub 0).val+i by omega]

/-- The concrete widened index component reads all occupied processor words,
accepts at its capacity, and installs the high bit, population and copied
digits with the prescribed call and probe bounds. -/
theorem index_stage_native (s : Sizes) (base : ℕ) (hw : 4 ≤ w) (advice : CutSchedule.Bits s.advice)
    (cuts : AllCuts s.h s.delta) (g : Fin (2^(s.h+1))) (sites : s.h+2 ≤ 2^d)
    (scratch : 2^d ≤ base) (fit : limit s base ≤ 2^w) :
    let pub := indexWords w s base
    let m := physicalMemory (d := d) hw advice cuts g
    let P := ((stageTemplate .index).2.instantiate w (rowData w s base .index)).program
    ∃ rs, runSegment P 25 (some 0) m (List.replicate (calls s .index) []) = some rs ∧
      endState (some 0) rs = none ∧ rs.length = calls s .index ∧
      (∀ rep ∈ rs, rep.probes ≤ probes .index) ∧
      LiveStageLink.PreservesTagOnReturns (Fin.ofNat _ base) m rs ∧
      PhysicalIndex (d := d) hw pub advice cuts g (after m (eventLog rs)) := by
  let pub := indexWords w s base
  let m := physicalMemory (d := d) hw advice cuts g
  let addr : Word w := Fin.ofNat _ base
  rw [limit_eq] at fit
  have va : (pub 0).val = indexBase base := by
    change (indexBase base) % (2^w) = _
    exact Nat.mod_eq_of_lt (by unfold indexBase; omega)
  have vh : (pub 1).val = highAddr s base := by
    change (highAddr s base) % (2^w) = _
    exact Nat.mod_eq_of_lt (by unfold highAddr indexBase; omega)
  have vc : (pub 2).val = populationAddr s base := by
    change (populationAddr s base) % (2^w) = _
    exact Nat.mod_eq_of_lt (by unfold populationAddr highAddr indexBase; omega)
  have vtag : addr.val = base := Nat.mod_eq_of_lt (by omega)
  have htag : addr.val < (pub 0).val := by rw [vtag, va]; unfold indexBase; omega
  have hcap : ((s.h+2 : ℕ) : Word w).val = s.h+2 := Fin.val_cast_of_lt (by omega)
  have hscratch : 2^d ≤ (pub 0).val := by rw [va]; unfold indexBase; omega
  have layout : ScanLayout pub (s.h+2) := ⟨sites.trans hscratch, by rw [vh,va]; rfl, by rw [vc,vh]; exact Nat.lt_succ_self _⟩
  obtain ⟨raw, hrun, _, hlen, hprobes, hindex⟩ :=
    physical_index_scan_native hw pub advice cuts g sites hscratch layout
  have hframe : LiveStageLink.PreservesTagOnReturns addr m raw :=
    runSegment_cursor_frame (indexTable.instantiate w pub).program 22 (s.h+2) addr
      (fun i hi mem rep he => index_step hw pub _ addr layout.highAfter layout.countAfter htag i hi mem [] rep he)
      0 (s.h+2) m raw (by omega) hrun
  let outs := raw.map LiveHeaderBounded.activeReport ++ [LiveHeaderBounded.closedReport w]
  have hcomplete := LiveHeaderBounded.runSegment_cursor_complete indexTable pub ((s.h+2 : ℕ) : Word w)
    (by decide : 0 < 22) 0 m (List.replicate (s.h+2) []) raw (by rw [List.length_replicate, Nat.zero_add, hcap]) hrun
    (fun i hi mem bits rep he => (index_step hw pub _ addr layout.highAfter layout.countAfter htag i (by rwa [hcap] at hi) mem bits rep he).1)
  refine ⟨outs, ?_, ?_, ?_, ?_, guarded_frame hframe, ?_⟩
  · change runSegment ((entry (LiveHeaderBounded.bounded indexTable)).2.instantiate w (rowData w s base .index)).program
      25 (some 0) m (List.replicate (s.h+2+1) []) = some outs
    rw [run_entry, index_row, List.replicate_succ']
    exact hcomplete
  · rw [show outs = raw.map LiveHeaderBounded.activeReport ++ [LiveHeaderBounded.closedReport w] from rfl, endState_append]
    rfl
  · simp [outs,hlen,calls]
  · intro rep hm
    rcases List.mem_append.mp hm with h | h
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
      exact hprobes x hx
    · obtain rfl := List.mem_singleton.mp h
      exact Nat.zero_le _
  · have hlast : after m (eventLog outs) = after m (eventLog (raw.map LiveHeaderBounded.activeReport)) := by
      simp only [outs, eventLog, List.flatMap_append, after, List.foldl_append, List.flatMap_singleton]
      rfl
    rw [hlast, LiveHeaderBounded.after_activeReports]
    exact hindex

end LiveHeaderProgram

end VPVNP
end Computability
end OAI

import OAI.Hierarchy.ProbeStagePrefixMemory
import OAI.Hierarchy.ProbeStageLeast

namespace OAI
/-! # Immutable native directory reads of the physical record procedure -/

namespace Hierarchy.ProbeStage.Native
open Computability.VPVNP.BurstRAM
open scoped Fin.CommRing
noncomputable section

variable {h d w : ℕ} (hd : 1≤d) (j : Fin (rounds d)) (m : Memory w) (rom : immutable h d w j m)

include hd rom in
theorem directory_bases (b : Fin (groupBlocks h d j.val)) :
    m (region h d j.val 0+b.val)=((region h d j.val 12+b.val*radix h d : ℕ) : Word w) ∧
    m (region h d j.val 1+b.val)=((region h d j.val 13+b.val*radix h d : ℕ) : Word w) ∧
    m (region h d j.val 2+b.val)=((region h d j.val 14+b.val*((radix h d)^4*fieldChunks h) : ℕ) : Word w) ∧
    m (region h d j.val 3+b.val)=((region h d j.val 15+b.val*((radix h d)^4*fieldChunks h) : ℕ) : Word w) := by
  have valid := b.isLt.trans_le (region_room hd j.isLt.le).1
  exact ⟨rom 0 b.val valid,rom 1 b.val valid,rom 2 b.val valid,rom 3 b.val valid⟩

include hd rom in
theorem row_offsets (r : MaskIndex (radix h d)) :
    m (region h d j.val 4+rowCode r)=(↑(rowCode r*fieldChunks h) : Word w) ∧
    m (region h d j.val 5+rowCode r)=(↑(rowCode r*stringLength h) : Word w) := by
  have valid := (rowCode_lt r).trans_le (region_room hd j.isLt.le).2.2.1
  exact ⟨rom 4 _ valid,rom 5 _ valid⟩

include hd rom in
theorem string_word (r : MaskIndex (radix h d)) (t : Fin (stringLength h)) :
    m (region h d j.val 6+(rowCode r*stringLength h+t.val)) =
      (((formatAdvice h d).row r t).val : Word w) := by
  let a : Fin ((radix h d)^4) := ⟨rowCode r,rowCode_lt r⟩
  have valid := (show a.val*stringLength h+t.val < (radix h d)^4*stringLength h from
    (Nat.add_lt_add_left t.isLt _).trans_le (by
      rw [← Nat.succ_mul]
      exact Nat.mul_le_mul_right _ a.isLt)).trans_le (region_room hd j.isLt.le).2.2.2.1
  have cell := rom 6 _ valid
  simp [arrayValue,a] at cell
  exact cell.trans (congrArg (fun n : ℕ => (n : Word w)) (stringAt_index (formatAdvice h d).row r t))

include rom in
theorem least_word (v : ℕ) (hv : v<2^fieldWidth h) :
    m (region h d j.val 7+v)=(MaskWords.least v : Word w) :=
  rom 7 _ (hv.trans_le (least_size h d))

include hd rom in
theorem occurrence_header (c : Fin (radix h d)) :
    m (region h d j.val 8+c.val)=(↑(c.val*directoryCapacity (radix h d) (stringLength h)) : Word w) ∧
    m (region h d j.val 9+c.val)=((PackedMask.occurrences (formatAdvice h d).row c).length : Word w) := by
  have valid := c.isLt.trans_le (region_room hd j.isLt.le).2.1
  refine ⟨rom 8 _ valid,?_⟩
  simpa [arrayValue,readFin_at] using rom 9 _ valid

include hd rom in
theorem occurrence_entries (c : Fin (radix h d)) (i : ℕ) (hi : i<(PackedMask.occurrences (formatAdvice h d).row c).length) :
    let index := c.val*directoryCapacity (radix h d) (stringLength h)+i
    let p := (PackedMask.occurrences (formatAdvice h d).row c)[i]
    m (region h d j.val 10+index)=(clearOffset (fieldWidth h) (fieldChunks h) p : Word w) ∧
      m (region h d j.val 11+index)=(clearWord (fieldWidth h) p : Word w) := by
  have valid := occurrence_offset hd c i hi
  have hit := occurrenceAt_index (formatAdvice h d).row c i hi
  constructor
  · have cell := rom 10 _ valid
    simp [arrayValue] at cell
    exact cell.trans (congrArg (fun o : Option (PackedMask.Pos (radix h d) (stringLength h)) =>
      ((o.map (clearOffset (fieldWidth h) (fieldChunks h))).getD 0 : Word w)) hit)
  · have cell := rom 11 _ valid
    simp [arrayValue] at cell
    exact cell.trans (congrArg (fun o : Option (PackedMask.Pos (radix h d) (stringLength h)) =>
      ((o.map (clearWord (fieldWidth h))).getD 0 : Word w)) hit)

end
end Hierarchy.ProbeStage.Native

end OAI

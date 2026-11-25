import OAI.ThreeFlat.Diagonal.TraceBucketMasks

namespace OAI
/-! # Canonical receiver addresses for the physical displacement masks -/

namespace Hierarchy.TraceReceiverMaskOrdinal

open ThreeFlat Diagonal LaneCursor RowLayout

theorem firstIndex_val (lane low : ℕ) (i : Fin (1+((lane+low)+(lane+low)))) :
    (firstIndex (fun j => (TracePhysical.laneRow (TracePhysical.offset (lane+low) j) : Row lane low)) i).val =
      if i.val=(lane+low)+1 then 1 else i.val := by
  let d := lane+low
  let off := fun j => (TracePhysical.laneRow (TracePhysical.offset d j) : Row lane low)
  have unique (z : Fin (1+(d+d))) (notDuplicate : z.val≠d+1) : firstIndex off z=z := by
    have first : firstMask off z=true := (TracePhysical.firstMask_eq lane low z).trans (decide_eq_true notDuplicate)
    have le : firstIndex off z≤z := Fin.find_le_of_pos (p:=fun j=>off j=off z) ⟨z,rfl⟩ rfl
    apply le_antisymm le
    apply le_of_not_gt
    intro earlier
    exact (of_decide_eq_true first) (firstIndex off z) earlier (first_eq off z)
  change (firstIndex off i).val = if i.val=d+1 then 1 else i.val
  split
  next duplicate =>
    have upper := i.isLt
    have positive : 0<d := by omega
    let j : Fin (1+(d+d)) := ⟨1,by omega⟩
    have same : off j=off i := by
      apply Fin.ext
      change (TracePhysical.offset d j).val=(TracePhysical.offset d i).val
      rw [TracePhysical.offset_nat,TracePhysical.offset_nat]
      simp [j,duplicate,TracePhysical.maskNat,show 1≤d by omega,show ¬d+1≤d by omega]
    rw [←firstIndex_congr off same,unique j (by change 1≠d+1;omega)]
  next good => rw [unique i good]

end Hierarchy.TraceReceiverMaskOrdinal

end OAI

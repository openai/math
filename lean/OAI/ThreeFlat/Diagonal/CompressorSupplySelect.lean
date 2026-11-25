import OAI.ThreeFlat.Diagonal.CompressorSupplyOrigins
import OAI.ThreeFlat.Diagonal.CompressorBitIntervals

namespace OAI
/-! # Port and balanced-copy lookup in the selected supply row -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.BitOrigins

open RAM.PhysicalPinsExpr
variable {n w d : ℕ} (pub : Param → ℕ) (mem : ℕ → ℕ) (vs : Fin n → ℕ)
local notation "V" => Formula.natural w pub mem vs

theorem portLookup_at (base first key : F n) (slots : List (Fin d)) (i : Fin d)
    (present : i ∈ slots)
    (lookup : ∀ j ∈ slots,mem (V base+(V first+j.val))=V key ↔ j=i) :
    V (portLookup base first key slots) = i.val := by
  induction slots with
  | nil => simp at present
  | cons a xs ih =>
    by_cases hit : a=i
    · have eq := (lookup a (by simp)).2 hit
      change (if decide (mem (V base+(V first+a.val))=V key) then a.val else
        V (portLookup base first key xs)) = i.val
      rw [ite_eq_left (by simpa using eq)]
      exact congrArg Fin.val hit
    · have ne := (lookup a (by simp)).not.mpr hit
      have rest : i∈xs := List.mem_cons.mp present |>.resolve_left (Ne.symm hit)
      change (if decide (mem (V base+(V first+a.val))=V key) then a.val else
        V (portLookup base first key xs)) = _
      rw [ite_eq_right (by simpa using ne)]
      exact ih rest (fun j h => lookup j (by simp [h]))

theorem portLookup_fin (base first key : F n) (i : Fin d)
    (lookup : ∀ j : Fin d,mem (V base+(V first+j.val))=V key ↔ j=i) :
    V (portLookup base first key (List.finRange d)) = i.val :=
  portLookup_at pub mem vs base first key _ i (List.mem_finRange _) (fun j _=>lookup j)


end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.BitOrigins

end OAI

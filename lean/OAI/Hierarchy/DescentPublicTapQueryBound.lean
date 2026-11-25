import OAI.Hierarchy.DescentFallbackQueryBounds
import OAI.Hierarchy.DescentPhysicalOperandLaws

namespace OAI
/-! # Original public tap and fallback stem tickets lie inside the native lookup -/
namespace Hierarchy.DescentResetPublicOperandBook.Config
open DescentSIMDLookup DescentFallbackOperandBranch DescentFallbackOperandQuery DescentResetLocalRoster
open DescentPacking.PackedMatch.Local DescentHostDirectory DescentFallbackItemSelect
noncomputable section
variable {n : ℕ} (C : Config)
local notation "F" => C.oldConfig

theorem old_item_stem (x : C.Data n) (side : Bool) (cap : ℕ)
    (donors : C.donors≤2^C.residual) (capRoom : C.oldCap≤cap) (j : Fin (F).count) :
    (F).stemAt side cap (C.oldItem x side j)≤2*total (F).toShape cap :=by
  apply (F).stem_bound
  · exact (finProdFinEquiv.symm j : Fin C.donors×Fin (2*C.oldCap)).1.isLt.trans_le donors
  · exact (finProdFinEquiv.symm j : Fin C.donors×Fin (2*C.oldCap)).2.isLt.trans_le (Nat.mul_le_mul_left _ capRoom)

theorem tap_query_bound (x : C.Data n) (side : Bool) (key : code C.residual)
    (mouth : DescentRotorOperandQueryROM.Shape.Mouth n)
    (donors : C.donors≤2^C.residual) (sectors : C.sectors=2^n) (capRoom : C.oldCap≤((C.reg x) 0).val)
    {output : ℕ×ℕ×ℕ×Bool} (got : C.tap x side key mouth=some output) :
    output.1≤2*total (F).toShape ((C.reg x) 0).val :=by
  classical
  unfold tap at got
  obtain ⟨prior,_,hit⟩:=Option.bind_eq_some_iff.mp got
  dsimp only at hit
  split at hit
  · cases hit
  · split at hit
    · cases hit
      apply directed_le
      apply (F).contact_position_bound side _ (.inl key) _ sectors
      change mouth.vertex.val<C.sectors+2^C.maxDepth
      rw [sectors]
      exact mouth.vertex.isLt.trans_le (Nat.le_add_right _ _)
    · obtain ⟨j,_,result⟩:=Option.bind_eq_some_iff.mp hit
      cases result
      exact C.old_item_stem x side _ donors capRoom _

end
end Hierarchy.DescentResetPublicOperandBook.Config

end OAI

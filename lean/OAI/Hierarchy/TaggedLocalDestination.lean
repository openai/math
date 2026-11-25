import OAI.Hierarchy.TaggedLocalDestinationData
import OAI.Hierarchy.TaggedAlignBlock
import OAI.Hierarchy.TaggedRadixStages
import OAI.Hierarchy.TaggedSortedBlock

namespace OAI
/-! # The physical alignment circuit realizes the deterministic destinations -/

namespace Hierarchy.Tagged.SortedBlock
open ThreeFlat Routing SortNetwork
open Radix.PassShape AlignRows
open scoped Classical
noncomputable section

variable {j t d w : ℕ} (digit : Fin d → Fin w) (real : Fin w) (x : Records (j+t) w)

private theorem sum_instances {A F : Type*} [AddCommMonoid F] (left right : Fintype A) (f : A → F) :
    (@Finset.univ A left).sum f=(@Finset.univ A right).sum f :=
  congrArg (fun a : Fintype A=>(@Finset.univ A a).sum f) (Subsingleton.elim left right)

theorem eval_align (F : Type*) [CommSemiring F] (ok : AlignedInput digit real x) (y : SortRelation.Data (j+t) w → Bool) :
    RadixStage.contract (AlignShell.shell (AlignRows.network F real digit)) (coeff F (j+t) w) (SortNetwork.pack x) y =
    if y = SortNetwork.pack (align digit real x) then 1 else 0 := by
  have out := AlignBlock.eval real digit x F (unwrap y) (prefixSize real x) (prefixSize_le real x)
    ok.front ok.ascending (placement digit real x ok) (fun i => Align.embed_val _ _ _ _ _)
  have eq : unwrap y = x ∘ (perm digit real x ok).symm ↔ y = SortNetwork.pack (align digit real x) := by
    rw [align,dite_eq_left ok]
    exact ⟨fun h => (pack_unwrap y).symm.trans (congrArg SortNetwork.pack h), fun h => (congrArg unwrap h).trans (unwrap_pack _)⟩
  simp only [RadixStage.contract,RadixStage.row,pack_unwrap,←eq,perm] at out ⊢
  exact (sum_instances _ _ _).trans out

end
end Hierarchy.Tagged.SortedBlock

end OAI

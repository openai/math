import OAI.Hierarchy.DescentSliceFields
import OAI.Hierarchy.DescentBundleExpose

namespace OAI
/-! # Fields and arity of a scalar recipe exposed as whole words -/
namespace Hierarchy.DescentBundleHistory
open DescentKernelHistory
open scoped Classical BigOperators
noncomputable section
variable {p : ℕ} (hp : 0<p) {Tag A : Type}

/-- Newly born raw table records publish a contiguous block for each real
role operand, with the correct number of empty or nonempty groups. -/
theorem fresh_tag (record : Recipe Tag A) (width : A→ℕ)
    (pub : ∀a,p∣width a) (priv : ∀h,p∣record.width h) (u : record.Node) :
    (((exposed record width hp pub priv).recipe hp).tag u)=
      (record.tag u,List.ofFn (fun j=>List.replicate (BitRecipe.referenceWidth record width (record.operand u j)/p)
        (⟨0,1,1⟩ : SliceCode))) := by
  refine (Shape.tag_fields hp (exposed record width hp pub priv) u).trans ?_
  apply congrArg (Prod.mk (record.tag u))
  change (List.ofFn fun j : Fin (record.arity u) =>
    List.ofFn fun _ : Fin (BitRecipe.referenceWidth record width (record.operand u j)/p) =>
      (⟨0,1,1⟩ : SliceCode)) = _
  simp only [List.ofFn_const]

theorem fresh_arity (record : Recipe Tag A) (width : A→ℕ)
    (pub : ∀a,p∣width a) (priv : ∀h,p∣record.width h) (u : record.Node) :
    (((exposed record width hp pub priv).recipe hp).arity u)=
      ∑j,BitRecipe.referenceWidth record width (record.operand u j)/p := by
  refine (Shape.recipe_refs hp (exposed record width hp pub priv) u).trans ?_
  change (∑ j : Fin (record.arity u),
    ∑ _ : Fin (BitRecipe.referenceWidth record width (record.operand u j)/p), (1 : ℕ)) = _
  simp

end
end Hierarchy.DescentBundleHistory

end OAI

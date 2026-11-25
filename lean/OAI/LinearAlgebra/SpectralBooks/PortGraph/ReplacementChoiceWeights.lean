import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementChoicePartition
import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementOldWeight

/-! # Summing the actual term indices chosen on each old map -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section

namespace PortGraph.ReplacementChoices.System

open scoped BigOperators Classical
open UniformDecorations PatchRecord

variable {N K : ℕ} {ε : ℝ} (C : System N K ε) (M : MapRep N)

variable {w : ℕ} {B : Type} [CommSemiring B]
    (Term : Checked N K ε → Type) (val : (R : Checked N K ε) → Term R → (R.val.shape.Stub → Bits w) → B)

variable [∀ R, Fintype (Term R)] (U : Tables B w)
    (localSum : ∀ (R : Checked N K ε) x, R.val.shape.oldValue U x = ∑ t, val R t x)

private theorem univ_congr {X : Type*} (i j : Fintype X) : @Finset.univ X i = @Finset.univ X j :=
  congrArg (fun k => @Finset.univ X k) (Subsingleton.elim i j)

include localSum in
/-- Multilinearity expands the entire old map into its actual choices of
one term on each canonical patch. -/
theorem eval_eq_sum_choices :
    eval M.map U = ∑ t : (C.family Term).Label M, C.choiceValue M Term val t := by
  let atStub (x : (C.pairing M).Wire → Bits w) (j : C.Occ M) (s : (C.record M j).shape.Stub) :=
    x (((C.pairing M).ends.symm ⟨j,s⟩).1)
  have factor : eval M.map U = ∑ x : (C.pairing M).Wire → Bits w,
      ∏ j, (C.record M j).shape.oldValue U (atStub x j) := by
    refine ((C.partition M).eval_eq_sum_records M.map (C.label M) (C.name M) U).trans ?_
    apply Finset.sum_congr (univ_congr _ _)
    intro x _
    rfl
  rw [factor]
  unfold choiceValue
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  refine Eq.trans ?_ (Fintype.prod_sum (fun j t => val (C.checked M j) t (atStub x j)))
  exact Finset.prod_congr rfl (fun j _ => localSum (C.checked M j) _)

include localSum in
/-- The old map-sum is indexed by a rooted isomorphism class and one actual
catalogue index on each of its certified occurrences. -/
theorem Z_eq_sum_choices :
    Z N w U = ∑ q : (C.family Term).Choices, C.choiceValue q.1.out Term val q.2 := by
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro m _
  rw [classEval_out]
  exact C.eval_eq_sum_choices m.out Term val U localSum

end PortGraph.ReplacementChoices.System

end

end SpectralBooks
end LinearAlgebra
end OAI

import OAI.LinearAlgebra.SpectralBooks.SiteTensor.SumDef
import Mathlib.Logic.Equiv.Sum

/-! # Tensor product distributes over the direct sum

The relabeling at each site sends a paired index with a left (respectively,
right) tag to a left (respectively, right) tagged pair. All sites must choose
the same tag for a coefficient of the direct sum to contribute.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor

variable {I K : Type*} [Fintype I] [Nonempty I] [CommSemiring K]
  {A B C : I → Type*} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)] [∀ i, Fintype (C i)]

/-- Left distributivity of the coefficient tensor product over the direct
sum, up to the canonical relabeling at each site. -/
theorem sumCoeff_product_distrib (T : (∀ i, A i) → K) (U : (∀ i, B i) → K)
    (V : (∀ i, C i) → K) (x : ∀ i, A i × (B i ⊕ C i)) :
    T (fun i => (x i).1) * sumCoeff U V (fun i => (x i).2) =
      sumCoeff (fun y : ∀ i, A i × B i => T (fun i => (y i).1) * U (fun i => (y i).2))
        (fun y : ∀ i, A i × C i => T (fun i => (y i).1) * V (fun i => (y i).2))
        (fun i => Equiv.prodSumDistrib _ _ _ (x i)) := by
  classical
  let u (i : I) := (x i).1
  let v (i : I) := (x i).2
  change T u * sumCoeff U V v = sumCoeff _ _ (fun i => Equiv.prodSumDistrib _ _ _ (u i, v i))
  generalize v = w
  by_cases hl : ∃ y : ∀ i, B i, (fun i => Sum.inl (y i)) = w
  · obtain ⟨y, rfl⟩ := hl
    simp only [Equiv.prodSumDistrib_apply_left, sumCoeff_inl]
  by_cases hr : ∃ y : ∀ i, C i, (fun i => Sum.inr (y i)) = w
  · obtain ⟨y, rfl⟩ := hr
    simp only [Equiv.prodSumDistrib_apply_right, sumCoeff_inr]
  have hleft (z : ∀ i, A i × B i) :
      (fun i => Sum.inl (z i)) ≠ (fun i => Equiv.prodSumDistrib _ _ _ (u i, w i)) := by
    intro eq
    refine hl ⟨fun i => (z i).2, funext fun i => ?_⟩
    have h := congrArg (fun t => ((Equiv.prodSumDistrib (A i) (B i) (C i)).symm t).2)
      (congrFun eq i)
    simpa using h
  have hright (z : ∀ i, A i × C i) :
      (fun i => Sum.inr (z i)) ≠ (fun i => Equiv.prodSumDistrib _ _ _ (u i, w i)) := by
    intro eq
    refine hr ⟨fun i => (z i).2, funext fun i => ?_⟩
    have h := congrArg (fun t => ((Equiv.prodSumDistrib (A i) (B i) (C i)).symm t).2)
      (congrFun eq i)
    simpa using h
  rw [sumCoeff_mixed _ _ _ (not_exists.mp hl) (not_exists.mp hr),
    sumCoeff_mixed _ _ _ hleft hright, mul_zero]

end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI

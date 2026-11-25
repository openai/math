import OAI.LinearAlgebra.SpectralBooks.SiteTensor.Raw

/-! # Sums of restrictions of a fixed tensor -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators Classical

namespace SiteTensor.Raw

universe v
variable {I K : Type*} [Fintype I] [CommSemiring K]

/-- A sum of local restrictions of a fixed tensor is a restriction of its product
with the common-label diagonal on the summand indices. -/
theorem restricts_diagonal_mul_of_coefficients {α : Type v} [Fintype α] {X Y : Raw.{v} I K}
    (h : ∃ M : ∀ (_ : α) i, X.Leg i → Y.Leg i → K, ∀ x,
      X.coeff x = ∑ a, ∑ y, Y.coeff y * ∏ i, M a i (x i) (y i)) :
    X.Restricts ((diagonal I K α).mul Y) := by
  classical
  obtain ⟨M, hM⟩ := h
  refine ⟨fun i x y => M y.1 i x y.2, fun x => ?_⟩
  rw [hM x]
  symm
  let e := Equiv.arrowProdEquivProdArrow I (fun _ => α) Y.Leg
  calc
    _ = ∑ p : (I → α) × (∀ i, Y.Leg i),
        (diagonal I K α).coeff p.1 * Y.coeff p.2 * ∏ i, M (p.1 i) i (x i) (p.2 i) :=
      Fintype.sum_equiv e _ _ fun _ => rfl
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [diagonal, Finset.sum_mul, ite_mul, one_mul, zero_mul]
      rw [Finset.sum_comm]
      conv_lhs => enter [2, y]; rw [Finset.sum_comm]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      exact Finset.sum_comm

end SiteTensor.Raw

end SpectralBooks
end LinearAlgebra
end OAI

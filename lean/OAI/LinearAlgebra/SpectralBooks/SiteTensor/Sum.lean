import OAI.LinearAlgebra.SpectralBooks.SiteTensor.SumDef

/-! # Direct sums preserve tensor restrictions -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators Classical

namespace SiteTensor

open Crossing

variable {I : Type*} [Fintype I] {K : Type*} [CommSemiring K]
variable {A B C D : I → Type*} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    [∀ i, Fintype (C i)] [∀ i, Fintype (D i)]

omit [∀ i, Fintype (C i)] in
/-- Pushing output indices after a restriction sums the rows of each local matrix
over the corresponding fibers. -/
theorem pushCoeff_restriction {X : (∀ i, B i) → K} {T : (∀ i, A i) → K}
    (M : ∀ i, B i → A i → K)
    (hM : ∀ x, X x = ∑ a, T a * ∏ i, M i (x i) (a i))
    (f : ∀ i, B i → C i) (y : ∀ i, C i) :
    pushCoeff (fun x i => f i (x i)) X y =
      ∑ a, T a * ∏ i, ∑ b, if f i b = y i then M i b (a i) else 0 := by
  simp only [Fintype.prod_sum, Finset.mul_sum, Fintype.prod_ite_zero, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  unfold pushCoeff
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hM x, funext_iff]
  split <;> simp [*]

/-- Apply the two given restrictions on their respective diagonal blocks. -/
theorem restrict_sum {X : (∀ i, B i) → K} {Y : (∀ i, D i) → K}
    {T : (∀ i, A i) → K} {U : (∀ i, C i) → K}
    (h : IsRestriction X T) (h' : IsRestriction Y U) :
    IsRestriction (sumCoeff X Y) (sumCoeff T U) := by
  obtain ⟨M, hM⟩ := h
  obtain ⟨N, hN⟩ := h'
  let L (i : I) : B i ⊕ D i → A i ⊕ C i → K
    | .inl b, .inl a => M i b a
    | .inr d, .inr c => N i d c
    | _, _ => 0
  refine ⟨L, fun y => ?_⟩
  simp only [sumCoeff, add_mul, Finset.sum_add_distrib, sum_pushCoeff_mul]
  rw [pushCoeff_restriction M hM, pushCoeff_restriction N hN]
  congr 1
  · refine Finset.sum_congr rfl fun a _ => congrArg (T a * ·) ?_
    refine Finset.prod_congr rfl fun i _ => ?_
    cases y i <;> simp [L]
  · refine Finset.sum_congr rfl fun c _ => congrArg (U c * ·) ?_
    refine Finset.prod_congr rfl fun i _ => ?_
    cases y i <;> simp [L]

end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI

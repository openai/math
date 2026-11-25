import OAI.Hierarchy.ProbeBudget

namespace OAI
/-! # Accounting for the retained and discarded routing selectors -/

namespace Hierarchy.TaggedPrune
open AdaptiveProbe
open scoped BigOperators Classical

variable {I : Type*} [Fintype I]

/-- Positive-scale links and cross-layer links have disjoint budgets. Spending
the required catalyst flow on cross-layer links leaves at most eleven units per
input record for every retained selector. -/
theorem positive_budget {p q Q Λ : ℝ} {n w M Nc : ℕ} {t len y : I → ℝ}
    {cross : Finset I} (hΛ : 0 ≤ Λ) (ht : ∀ i, 0 ≤ t i) (hl : ∀ i, 0 ≤ len i)
    (hy : ∀ i, 0 ≤ y i) (cross_zero : ∀ i ∈ cross, t i = 0)
    (budget : TermBudget p q Q Λ n w M Nc t len y)
    (kept : 2*(M:ℝ)*Nc/w - n ≤ ∑ i ∈ cross, len i*y i) :
    (∑ i ∈ Finset.univ.filter (fun i => 0 < t i),
      (len i*y i + Λ*capacity p q Q (t i) (len i))) ≤ 11*(n:ℝ) := by
  let b (i : I) := len i*y i + Λ*capacity p q Q (t i) (len i)
  have hb (i : I) : 0 ≤ b i := by
    refine add_nonneg (mul_nonneg (hl i) (hy i)) (mul_nonneg hΛ ?_)
    unfold capacity
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (Real.rpow_nonneg (ht i) _) ((Real.rpow_nonneg (hl i) _).trans (le_max_left _ _))
  let pos := Finset.univ.filter fun i => 0 < t i
  have disj : Disjoint pos cross := by
    apply Finset.disjoint_left.mpr
    intro i hi hc
    exact (Finset.mem_filter.mp hi).2.ne' (cross_zero i hc)
  have hsum : (∑ i ∈ pos, b i) + ∑ i ∈ cross, b i ≤ ∑ i, b i := by
    rw [← Finset.sum_union disj]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by
      intro i _ _; exact hb i)
  have hcross : ∑ i ∈ cross, b i = ∑ i ∈ cross, len i*y i := by
    exact Finset.sum_congr rfl (fun i hi => by simp [b,cross_zero i hi])
  rw [hcross] at hsum
  change (∑ i ∈ pos, b i) ≤ _
  change (∑ i, b i) ≤ _ at budget
  linarith

/-- If the cross-layer test rejects, placing the layers at scale `1/M`
gives the stated discount in the price of that particular summand. -/
theorem discarded_price {n w M Nc : ℕ} (hw : 0<w) (hM : 0<M)
    {crossPrice normalizedCharge : ℝ}
    (placement : crossPrice ≤ (w:ℝ)/M*normalizedCharge)
    (rejected : normalizedCharge < 2*(M:ℝ)*Nc/w-n) :
    crossPrice < 2*(Nc:ℝ)-(n:ℝ)*w/M := by
  have hm : 0 < (M:ℝ) := Nat.cast_pos.mpr hM
  have hww : 0 < (w:ℝ) := Nat.cast_pos.mpr hw
  apply placement.trans_lt ((mul_lt_mul_of_pos_left rejected (div_pos hww hm)).trans_eq ?_)
  field_simp


end Hierarchy.TaggedPrune

end OAI

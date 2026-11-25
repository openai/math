import OAI.Optimization.LinearProgramming.Compression.SeparationBasic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

open scoped BigOperators

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

private theorem sum_on_subset {ι : Type*} [DecidableEq ι] {s t : Finset ι}
    (h : s ⊆ t) (f : ι → ℝ) :
    (∑ i ∈ t, if i ∈ s then f i else 0) = ∑ i ∈ s, f i := by
  rw [← Finset.sum_extend_by_zero s f]
  exact (Finset.sum_subset h fun i _ hi ↦ by simp [hi]).symm

/-- The overlap of the two subsets cancels, so the error is paid at most once per index. -/
theorem subsetSum_sub_error {ι : Type*} [DecidableEq ι] {J A B : Finset ι}
    (hA : A ⊆ J) (hB : B ⊆ J) (e : ι → ℝ) {η : ℝ} (hη : 0 ≤ η)
    (he : ∀ i ∈ J, |e i| ≤ η) :
    |(∑ i ∈ A, e i) - ∑ i ∈ B, e i| ≤ (J.card : ℝ) * η := by
  rw [← sum_on_subset hA e, ← sum_on_subset hB e, ← Finset.sum_sub_distrib]
  calc
    _ ≤ _ := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ J, η := by
      refine Finset.sum_le_sum fun i hi ↦ ?_
      by_cases h₁ : i ∈ A <;> by_cases h₂ : i ∈ B <;> simp [h₁, h₂, hη, he i hi]
    _ = _ := by simp

/-- A proxy error of at most one in a difference leaves more than one unit of separation. -/
theorem IsDissociated.true_log_separation {ι : Type*} [DecidableEq ι]
    {l ell : ι → ℝ} {J : Finset ι} (hd : IsDissociated l J)
    {η : ℝ} (hη : 0 ≤ η) (hsmall : (J.card : ℝ) * η ≤ 1)
    (herr : ∀ i ∈ J, |l i - ell i| ≤ η)
    {A B : Finset ι} (hA : A ⊆ J) (hB : B ⊆ J) (hne : A ≠ B) :
    1 < |(∑ i ∈ A, ell i) - ∑ i ∈ B, ell i| := by
  have he := (subsetSum_sub_error hA hB (fun i ↦ l i - ell i) hη herr).trans hsmall
  have hd' := hd A hA B hB hne
  simp only [Finset.sum_sub_distrib] at he
  set p := (∑ i ∈ A, l i) - ∑ i ∈ B, l i
  set q := (∑ i ∈ A, ell i) - ∑ i ∈ B, ell i
  have he' : |p - q| ≤ 1 := by
    convert he using 2
    dsimp [p, q]
    ring
  have htriangle : |p| ≤ |p-q| + |q| := by simpa using abs_add_le (p-q) q
  change 2 < |p| at hd'
  linarith

private theorem factor_two_of_log_lt {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (h : Real.logb 2 x + 1 < Real.logb 2 y) : 2 * x < y := by
  apply (Real.logb_lt_logb_iff (b := 2) (by norm_num) (by positivity) hy).mp
  rw [Real.logb_mul (by norm_num) hx.ne', Real.logb_self_eq_one (by norm_num)]
  linarith

/-- Distinct subproducts of the original signed minor values are separated in magnitude. -/
theorem IsDissociated.subsetProduct_doubling {ι : Type*} [DecidableEq ι]
    {l x : ι → ℝ} {J : Finset ι} (hd : IsDissociated l J)
    {η : ℝ} (hη : 0 ≤ η) (hsmall : (J.card : ℝ) * η ≤ 1)
    (hn : ∀ i ∈ J, x i ≠ 0) (herr : ∀ i ∈ J, |l i - Real.logb 2 (|x i|)| ≤ η)
    {A B : Finset ι} (hA : A ⊆ J) (hB : B ⊆ J) (hne : A ≠ B) :
    2 * |∏ i ∈ A, x i| < |∏ i ∈ B, x i| ∨
    2 * |∏ i ∈ B, x i| < |∏ i ∈ A, x i| := by
  have hsep := hd.true_log_separation hη hsmall herr hA hB hne
  simp only [Real.logb_abs] at hsep
  have hAn : ∀ i ∈ A, x i ≠ 0 := fun i hi ↦ hn i (hA hi)
  have hBn : ∀ i ∈ B, x i ≠ 0 := fun i hi ↦ hn i (hB hi)
  rw [← Real.logb_prod A x hAn, ← Real.logb_prod B x hBn] at hsep
  have hAp := abs_pos.mpr (Finset.prod_ne_zero_iff.mpr hAn)
  have hBp := abs_pos.mpr (Finset.prod_ne_zero_iff.mpr hBn)
  rcases lt_abs.mp hsep with h | h
  · right; apply factor_two_of_log_lt hBp hAp; simp only [Real.logb_abs]; linarith
  · left; apply factor_two_of_log_lt hAp hBp; simp only [Real.logb_abs]; linarith

end Compression
end LinearProgramming
end Optimization
end OAI

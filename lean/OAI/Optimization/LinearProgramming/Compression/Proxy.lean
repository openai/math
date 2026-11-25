import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Exact sign queries for the hybrid small and large logarithm representation in §3.4. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Contribution of the rational small-log proxies after clearing their common denominator. -/
def clearedProxyOffset (large : Finset ι) (D : ℕ) (c : ℤ) (a grid : ι → ℤ) : ℤ :=
  D * c + ∑ i ∈ Finset.univ \ large, a i * grid i

/-- In the large-log branch the scalar to compare to one is this positive rational. -/
def proxyProduct (large : Finset ι) (D : ℕ) (c : ℤ) (a grid : ι → ℤ)
    (mag : ι → ℚ) : ℚ :=
  2 ^ clearedProxyOffset large D c a grid * ∏ i ∈ large, mag i ^ ((D : ℤ) * a i)

/-- The mathematical quantity represented by a mixture of grid points and symbolic logs. -/
noncomputable def proxyAffine (large : Finset ι) (D : ℕ) (c : ℤ) (a grid : ι → ℤ)
    (mag : ι → ℚ) : ℝ :=
  c + ∑ i, (a i : ℝ) * (if i ∈ large then Real.logb 2 (mag i) else (grid i : ℝ) / D)

private theorem logb_zpow' (x : ℝ) (n : ℤ) :
    Real.logb 2 (x ^ n) = n * Real.logb 2 x := by
  simp [Real.logb, Real.log_zpow, mul_div_assoc]

private theorem clearedProxyOffset_add (large : Finset ι) (D : ℕ) (hD : 0 < D)
    (c : ℤ) (a grid : ι → ℤ) (mag : ι → ℚ) :
    (clearedProxyOffset large D c a grid : ℝ) +
      ∑ i ∈ large, ((D : ℝ) * a i) * Real.logb 2 (mag i) =
    D * proxyAffine large D c a grid mag := by
  have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  rw [proxyAffine, mul_add, Finset.mul_sum]
  rw [← Finset.sum_sdiff (Finset.subset_univ large)]
  simp only [clearedProxyOffset, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_sum]
  have hsmall :
      (∑ i ∈ Finset.univ \ large, (D : ℝ) * ((a i : ℝ) *
        (if i ∈ large then Real.logb 2 (mag i) else (grid i : ℝ) / D))) =
       ∑ i ∈ Finset.univ \ large, (a i : ℝ) * grid i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [ite_eq_right (Finset.mem_sdiff.mp hi).2]
    field_simp
  have hlarge :
      (∑ i ∈ large, (D : ℝ) * ((a i : ℝ) *
        (if i ∈ large then Real.logb 2 (mag i) else (grid i : ℝ) / D))) =
       ∑ i ∈ large, ((D : ℝ) * a i) * Real.logb 2 (mag i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [ite_eq_left hi, mul_assoc]
  rw [hsmall, hlarge, add_assoc]

/-- Exponentiation of the cleared affine form is exact, including negative exponents.
The finite product is formed in the rationals. -/
theorem logb_proxyProduct (large : Finset ι) (D : ℕ) (hD : 0 < D)
    (c : ℤ) (a grid : ι → ℤ) (mag : ι → ℚ) (hmag : ∀ i ∈ large, 0 < mag i) :
    Real.logb 2 (proxyProduct large D c a grid mag) = D * proxyAffine large D c a grid mag := by
  have hpow (i) (hi : i ∈ large) : (0 : ℝ) < (mag i : ℝ) ^ ((D : ℤ) * a i) :=
    zpow_pos (by exact_mod_cast hmag i hi) _
  unfold proxyProduct
  push_cast
  rw [Real.logb_mul (by positivity) (Finset.prod_pos fun i hi => hpow i hi).ne',
    logb_zpow', Real.logb_self_eq_one (by norm_num), mul_one,
    Real.logb_prod _ _ (fun i hi => (hpow i hi).ne')]
  simp only [logb_zpow', Int.cast_mul, Int.cast_natCast]
  exact clearedProxyOffset_add large D hD c a grid mag

private theorem pos_mul_neg_iff {x y : ℝ} (hx : 0 < x) : x * y < 0 ↔ y < 0 := by
  constructor
  · intro h
    by_contra! hn
    exact (mul_nonneg hx.le hn).not_gt h
  · exact mul_neg_of_pos_of_neg hx

private def orderTest {α : Type*} [LinearOrder α] (x y : α) : Ordering :=
  if x < y then .lt else if y < x then .gt else .eq

/-- The proxy comparison uses no analytic operations. When no symbolic log occurs it only
compares the integer numerator to zero. -/
def compareProxyAffine (large : Finset ι) (D : ℕ) (c : ℤ) (a grid : ι → ℤ)
    (mag : ι → ℚ) : Ordering :=
  if large.Nonempty then orderTest (proxyProduct large D c a grid mag) 1
  else orderTest (clearedProxyOffset large D c a grid) 0

/-- All three outcomes of the rational comparison agree with the true affine form. -/
theorem compareProxyAffine_correct (large : Finset ι) (D : ℕ) (hD : 0 < D)
    (c : ℤ) (a grid : ι → ℤ) (mag : ι → ℚ) (hmag : ∀ i ∈ large, 0 < mag i) :
    compareProxyAffine large D c a grid mag =
      (if proxyAffine large D c a grid mag < 0 then .lt
       else if 0 < proxyAffine large D c a grid mag then .gt else .eq) := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  by_cases hl : large.Nonempty
  · rw [compareProxyAffine, ite_eq_left hl]
    have hp : 0 < proxyProduct large D c a grid mag :=
      mul_pos (zpow_pos (by norm_num) _) (Finset.prod_pos fun i hi => zpow_pos (hmag i hi) _)
    have hr : (0 : ℝ) < proxyProduct large D c a grid mag := by exact_mod_cast hp
    have hn := Real.logb_neg_iff (by norm_num : (1 : ℝ) < 2) hr
    have hpos := Real.logb_pos_iff (by norm_num : (1 : ℝ) < 2) hr
    rw [logb_proxyProduct large D hD c a grid mag hmag, pos_mul_neg_iff hD'] at hn
    rw [logb_proxyProduct large D hD c a grid mag hmag, mul_pos_iff_of_pos_left hD'] at hpos
    have hn' : proxyAffine large D c a grid mag < 0 ↔ proxyProduct large D c a grid mag < 1 := by
      exact_mod_cast hn
    have hpos' : 0 < proxyAffine large D c a grid mag ↔ 1 < proxyProduct large D c a grid mag := by
      exact_mod_cast hpos
    simp only [orderTest, hn', hpos']
  · rw [compareProxyAffine, ite_eq_right hl]
    have hempty := Finset.not_nonempty_iff_eq_empty.mp hl
    subst large
    have he := clearedProxyOffset_add (∅ : Finset ι) D hD c a grid mag
    simp only [Finset.sum_empty, add_zero] at he
    have hn : (clearedProxyOffset ∅ D c a grid : ℝ) < 0 ↔ proxyAffine ∅ D c a grid mag < 0 := by
      rw [he, pos_mul_neg_iff hD']
    have hp : (0 : ℝ) < clearedProxyOffset ∅ D c a grid ↔ 0 < proxyAffine ∅ D c a grid mag := by
      rw [he, mul_pos_iff_of_pos_left hD']
    have hn' : clearedProxyOffset ∅ D c a grid < 0 ↔ proxyAffine ∅ D c a grid mag < 0 := by
      exact_mod_cast hn
    have hp' : 0 < clearedProxyOffset ∅ D c a grid ↔ 0 < proxyAffine ∅ D c a grid mag := by
      exact_mod_cast hp
    simp only [orderTest, hn', hp']

end Compression
end LinearProgramming
end Optimization
end OAI

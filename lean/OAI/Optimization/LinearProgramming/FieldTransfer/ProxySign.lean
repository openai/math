import OAI.Optimization.LinearProgramming.Compression.Proxy

/-! Implementing integer affine comparisons of hybrid proxies for arbitrary positive **real**
minor magnitudes. Only the proof interprets a symbolic large magnitude by its logarithm. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace FieldTransfer
namespace RealProxy

open scoped BigOperators
open OAI.Optimization.LinearProgramming.Compression (clearedProxyOffset)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def affineLog (large : Finset ι) (D : ℕ) (c : ℤ) (a grid : ι → ℤ)
    (mag : ι → ℝ) : ℝ :=
  c + ∑ i, (a i : ℝ) * (if i ∈ large then Real.logb 2 (mag i) else (grid i : ℝ)/D)

/-- Evaluate the multiplicative comparison with constant two, integer powers and multiplication. -/
noncomputable def powerProduct (large : Finset ι) (D : ℕ) (c : ℤ) (a grid : ι → ℤ)
    (mag : ι → ℝ) : ℝ :=
  2 ^ clearedProxyOffset large D c a grid * ∏ i ∈ large, mag i ^ ((D : ℤ) * a i)

private theorem scaled_affine (large : Finset ι) (D : ℕ) (hD : 0 < D)
    (c : ℤ) (a grid : ι → ℤ) (mag : ι → ℝ) :
    D * affineLog large D c a grid mag = (clearedProxyOffset large D c a grid : ℝ) +
      ∑ i ∈ large, ((D : ℝ) * a i) * Real.logb 2 (mag i) := by
  have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  rw [affineLog, mul_add, Finset.mul_sum, ← Finset.sum_sdiff (Finset.subset_univ large)]
  simp only [clearedProxyOffset, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_sum]
  have hsmall : (∑ i ∈ Finset.univ \ large, (D : ℝ) * ((a i : ℝ) *
      (if i ∈ large then Real.logb 2 (mag i) else (grid i : ℝ)/D))) =
      ∑ i ∈ Finset.univ \ large, (a i : ℝ) * grid i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [ite_eq_right (Finset.mem_sdiff.mp hi).2]
    field_simp
  have hlarge : (∑ i ∈ large, (D : ℝ) * ((a i : ℝ) *
      (if i ∈ large then Real.logb 2 (mag i) else (grid i : ℝ)/D))) =
      ∑ i ∈ large, ((D : ℝ) * a i) * Real.logb 2 (mag i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [ite_eq_left hi, mul_assoc]
  rw [hsmall, hlarge, add_assoc]

/-- Clearing the common dyadic denominator leaves nonalgebraic logarithms only at the
indices marked large by the range scan. -/
theorem clear_affine_log (large : Finset ι) (D : ℕ) (hD : 0 < D)
    (c : ℤ) (a grid : ι → ℤ) (mag : ι → ℝ) :
    D * affineLog large D c a grid mag = (clearedProxyOffset large D c a grid : ℝ) +
      ∑ i ∈ large, ((D : ℝ) * a i) * Real.logb 2 (mag i) :=
  scaled_affine large D hD c a grid mag

theorem logb_powerProduct (large : Finset ι) (D : ℕ) (hD : 0 < D)
    (c : ℤ) (a grid : ι → ℤ) (mag : ι → ℝ) (hm : ∀ i ∈ large, 0 < mag i) :
    Real.logb 2 (powerProduct large D c a grid mag) = D * affineLog large D c a grid mag := by
  have hp (i) (hi : i ∈ large) : 0 < mag i ^ ((D : ℤ) * a i) := zpow_pos (hm i hi) _
  have logpow (x : ℝ) (n : ℤ) : Real.logb 2 (x^n) = n * Real.logb 2 x := by
    simp [Real.logb, Real.log_zpow, mul_div_assoc]
  rw [powerProduct, Real.logb_mul (by positivity) (Finset.prod_pos hp).ne', logpow,
    Real.logb_self_eq_one (by norm_num), mul_one, Real.logb_prod _ _ (fun i hi => (hp i hi).ne'),
    scaled_affine large D hD]
  simp [logpow]

private def compareInputs {α : Type*} [LinearOrder α] (x y : α) : Ordering :=
  if x < y then .lt else if y < x then .gt else .eq

private theorem mul_neg_left {x y : ℝ} (hx : 0 < x) : x*y < 0 ↔ y < 0 := by
  simpa using (mul_lt_mul_iff_right₀ hx : x*y < x*0 ↔ y < 0)

noncomputable def compareAffine (large : Finset ι) (D : ℕ) (c : ℤ) (a grid : ι → ℤ)
    (mag : ι → ℝ) : Ordering :=
  if large.Nonempty then compareInputs (powerProduct large D c a grid mag) 1
  else compareInputs (clearedProxyOffset large D c a grid) 0

/-- The answers -1, 0 and +1 all agree with the same affine form. -/
theorem compareAffine_correct (large : Finset ι) (D : ℕ) (hD : 0 < D)
    (c : ℤ) (a grid : ι → ℤ) (mag : ι → ℝ) (hm : ∀ i ∈ large, 0 < mag i) :
    compareAffine large D c a grid mag =
      (if affineLog large D c a grid mag < 0 then .lt
      else if 0 < affineLog large D c a grid mag then .gt else .eq) := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  let v := affineLog large D c a grid mag
  by_cases hl : large.Nonempty
  · rw [compareAffine, ite_eq_left hl]
    have hp : 0 < powerProduct large D c a grid mag :=
      mul_pos (zpow_pos (by norm_num) _) (Finset.prod_pos fun i hi => zpow_pos (hm i hi) _)
    have hn := Real.logb_neg_iff (by norm_num : (1:ℝ)<2) hp
    have hpos := Real.logb_pos_iff (by norm_num : (1:ℝ)<2) hp
    rw [logb_powerProduct large D hD c a grid mag hm] at hn hpos
    have hv : (v < 0) ↔ powerProduct large D c a grid mag < 1 := by
      simpa [v, mul_neg_left hD'] using hn
    have hv' : (0 < v) ↔ 1 < powerProduct large D c a grid mag := by
      simpa [v, mul_pos_iff_of_pos_left hD'] using hpos
    change compareInputs _ _ = if v < 0 then _ else if 0 < v then _ else _
    simp only [compareInputs, hv, hv']
  · have he := Finset.not_nonempty_iff_eq_empty.mp hl
    subst large
    have hv := scaled_affine (∅ : Finset ι) D hD c a grid mag
    simp only [Finset.sum_empty, add_zero] at hv
    have hn : clearedProxyOffset ∅ D c a grid < 0 ↔ affineLog ∅ D c a grid mag < 0 := by
      have hx : (clearedProxyOffset ∅ D c a grid : ℝ) < 0 ↔ affineLog ∅ D c a grid mag < 0 := by
        rw [← hv, mul_neg_left hD']
      exact_mod_cast hx
    have hp : 0 < clearedProxyOffset ∅ D c a grid ↔ 0 < affineLog ∅ D c a grid mag := by
      have hx : (0:ℝ) < clearedProxyOffset ∅ D c a grid ↔ 0 < affineLog ∅ D c a grid mag := by
        rw [← hv, mul_pos_iff_of_pos_left hD']
      exact_mod_cast hx
    simp [compareAffine, compareInputs, hn, hp]

end RealProxy
end FieldTransfer
end LinearProgramming
end Optimization
end OAI

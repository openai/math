import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

/-! # The rounded spectral-repair window -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section

section

/-- The first exponent `r` for which `2^r ≥ 2m`. -/
def repairWindowR (m : ℕ) : ℕ := Nat.clog 2 (2 * m)

/-- The integer radius used for the shifted count. -/
def repairWindowRadius (ℓ m : ℕ) : ℕ :=
  (ℓ - 1) * ⌈Real.sqrt (2 * (m : ℝ) * repairWindowR m)⌉₊

/-- The exponential bound at the manuscript's rounded radius is at most `1/(2m³)`. -/
theorem repairWindow_exp_le {ℓ m : ℕ} (hℓ : 2 ≤ ℓ) (hm : 2 ≤ m) :
    2 * Real.exp (-2 * (repairWindowRadius ℓ m : ℝ) ^ 2 / (m * ((ℓ : ℝ) - 1) ^ 2)) ≤
      1 / (2 * (m : ℝ) ^ 3) := by
  let r := repairWindowR m
  let d : ℝ := (ℓ : ℝ) - 1
  let c : ℕ := ⌈Real.sqrt (2 * (m : ℝ) * r)⌉₊
  have hd : 0 < d := by dsimp [d]; exact_mod_cast (by omega : 0 < (ℓ : ℤ) - 1)
  have hm₀ : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hradius : (repairWindowRadius ℓ m : ℝ) = d * c := by
    rw [repairWindowRadius, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ ℓ), Nat.cast_one]
  have hr : 0 ≤ 2 * (m : ℝ) * r := by positivity
  have hs : 2 * (m : ℝ) * r ≤ (c : ℝ) ^ 2 := by
    calc
      _ = Real.sqrt (2 * (m : ℝ) * r) ^ 2 := (Real.sq_sqrt hr).symm
      _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) (Nat.le_ceil _) _
  have he : -2 * (repairWindowRadius ℓ m : ℝ) ^ 2 / (m * d ^ 2) ≤ -4 * r := by
    apply (div_le_iff₀ (mul_pos hm₀ (sq_pos_of_pos hd))).mpr
    rw [hradius]
    nlinarith only [mul_le_mul_of_nonneg_left hs (sq_nonneg d)]
  have hc : 2 * (m : ℝ) ≤ (2 : ℝ) ^ r := by
    exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) (2 * m)
  have he₂ : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  have hpow : 2 * (m : ℝ) ≤ Real.exp r := by
    calc
      _ ≤ (2 : ℝ) ^ r := hc
      _ ≤ Real.exp 1 ^ r := pow_le_pow_left₀ (by norm_num) he₂ _
      _ = Real.exp r := by rw [← Real.exp_nat_mul]; simp
  have he₄ : Real.exp (-4 * r) = (Real.exp r ^ 4)⁻¹ := by
    rw [← Real.exp_nat_mul, ← Real.exp_neg]
    norm_num
  calc
    _ ≤ 2 * Real.exp (-4 * r) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by norm_num)
    _ = 2 / (Real.exp r) ^ 4 := by rw [he₄, div_eq_mul_inv]
    _ ≤ 2 / (2 * (m : ℝ)) ^ 4 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      exact pow_le_pow_left₀ (by positivity) hpow _
    _ ≤ _ := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith only [mul_nonneg (show 0 ≤ (m : ℝ) - 1 by exact_mod_cast (by omega : 0 ≤ (m : ℤ) - 1))
        (pow_nonneg hm₀.le 3), pow_nonneg hm₀.le 3]

end

end

end FiniteFourier
end LinearAlgebra
end OAI

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! # Summing the costs of recursive equality tests -/

namespace OAI
namespace Combinatorics
namespace Sunflower

/-- Each increment uses up at most the difference between two successive
terms of a geometrically decreasing reserve. -/
theorem filterRatio_bounded_of_affine {f : ℕ → ℝ} {A d : ℝ} (hd : 0 < d)
    (hstep : ∀ b : ℕ, f (b + 1) ≤ f b + (2 : ℝ) ^ (A - d * (b : ℝ))) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ b, f b ≤ M := by
  let q := (2 : ℝ) ^ (-d)
  have hq : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_lt_zero.mpr hd)
  have hq₀ : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  let reserve := (2 : ℝ) ^ A / (1 - q)
  have hr : reserve * (1 - q) = (2 : ℝ) ^ A := by
    exact div_mul_cancel₀ _ (sub_ne_zero.mpr hq.ne')
  have hr₀ : 0 ≤ reserve := div_nonneg (Real.rpow_nonneg (by norm_num) _) (sub_nonneg.mpr hq.le)
  have budget (b : ℕ) : f b + reserve * q ^ b ≤ f 0 + reserve := by
    induction b with
    | zero => simp
    | succ b ih =>
      have h := hstep b
      rw [show A - d * (b : ℝ) = A + -d * (b : ℝ) by ring,
        Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_mul_natCast (by norm_num)] at h
      change f (b + 1) ≤ f b + (2 : ℝ) ^ A * q ^ b at h
      rw [← hr] at h
      rw [pow_succ]
      linarith only [h, ih]
  refine ⟨max 1 (f 0 + reserve), le_max_left .., fun b => ?_⟩
  exact (le_add_of_nonneg_right (mul_nonneg hr₀ (pow_nonneg hq₀ _))).trans
    ((budget b).trans (le_max_right ..))

/-- There are at least `2^b` nonzero matching indices on `b+1` bits. -/
theorem matchingIndex_log_lower (b : ℕ) :
    (b : ℝ) ≤ Real.logb 2 ((2 ^ (b + 1) - 1 : ℕ) : ℝ) := by
  have h : 2 ^ b ≤ 2 ^ (b + 1) - 1 := by
    have hp : 0 < 2 ^ b := pow_pos (by decide) _
    rw [pow_succ]
    omega
  have h' : (2 : ℝ) ^ b ≤ ((2 ^ (b + 1) - 1 : ℕ) : ℝ) := by exact_mod_cast h
  have hp : 0 < ((2 ^ (b + 1) - 1 : ℕ) : ℝ) := (pow_pos (by norm_num) _).trans_le h'
  apply (Real.le_logb_iff_rpow_le (by norm_num) hp).2
  simpa using h'

/-- Dividing a correction by the price of all nonzero matching indices
leaves an exponentially decaying increment. The correction cost is measured
in base-two logarithms. -/
theorem filterIncrement_le_of_cost (b : ℕ) {u v θ d B : ℝ}
    (hu : 0 < u) (hv : 0 < v) (hθ : 0 ≤ θ)
    (hc : Real.logb 2 u - Real.logb 2 v ≤ (θ - d) * ((b : ℝ) + 1) + B) :
    u / (v * ((2 ^ (b + 1) - 1 : ℕ) : ℝ) ^ θ) ≤
      (2 : ℝ) ^ ((B + θ - d) - d * (b : ℝ)) := by
  have hl : 0 < ((2 ^ (b + 1) - 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt (Nat.one_lt_two_pow (by omega : b + 1 ≠ 0))
  have hpow := Real.rpow_pos_of_pos hl θ
  apply (Real.logb_le_iff_le_rpow (by norm_num) (div_pos hu (mul_pos hv hpow))).1
  rw [Real.logb_div hu.ne' (mul_pos hv hpow).ne', Real.logb_mul hv.ne' hpow.ne',
    Real.logb_rpow_eq_mul_logb_of_pos hl]
  linarith only [hc, mul_le_mul_of_nonneg_left (matchingIndex_log_lower b) hθ]

/-- For any strictly positive gap a single integral coding parameter makes
the two broadcast overhead slopes strictly smaller than half the gap. -/
theorem exists_broadcastParameter {θ g : ℝ} (hg : 0 < g) :
    ∃ h : ℕ, 1 ≤ h ∧ (12 / (h : ℝ)) * θ < g / 2 := by
  obtain ⟨n, hn⟩ := exists_nat_gt (24 * θ / g)
  refine ⟨n + 1, by omega, ?_⟩
  have hn' : 24 * θ < (n : ℝ) * g := (div_lt_iff₀ hg).mp hn
  rw [div_mul_eq_mul_div]
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < (↑(n + 1) : ℝ))).mpr
  push_cast
  linarith

end Sunflower
end Combinatorics
end OAI

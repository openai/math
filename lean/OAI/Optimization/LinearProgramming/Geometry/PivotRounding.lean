import OAI.Optimization.LinearProgramming.Geometry.Exponential
import OAI.Optimization.LinearProgramming.Geometry.Clipping

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

open SignType

/-- Change the overall sign of the row so the maximizing pivot becomes positive. -/
def pivotRound {n : ℕ} (raw f price : Fin n → ℚ) (p : Fin n) (B : ℕ) (j : Fin n) : ℚ :=
  (sign (raw p) : ℚ) * (sign (raw j) : ℚ) *
    roundedPower ((f j - price j) - (f p - price p)) B

@[simp] theorem pivotRound_zero {n : ℕ} (raw f price : Fin n → ℚ) (p : Fin n) (B : ℕ)
    (j : Fin n) (h : raw j = 0) : pivotRound raw f price p B j = 0 := by simp [pivotRound, h]

theorem pivotRound_pivot {n : ℕ} (raw f price : Fin n → ℚ) (p : Fin n) (B : ℕ)
    (hp : raw p ≠ 0) : pivotRound raw f price p B p = 1 := by
  rcases lt_or_gt_of_ne hp with h | h <;> simp [pivotRound, sign_neg, sign_pos, h]

theorem abs_pivotRound_le_one {n : ℕ} (raw f price : Fin n → ℚ) (p : Fin n) (B : ℕ)
    (j : Fin n) : |pivotRound raw f price p B j| ≤ 1 := by
  have hs (a : SignType) : |(a : ℚ)| ≤ 1 := by cases a <;> norm_num
  have h := roundedPower_bounds ((f j - price j) - (f p - price p)) B
  rw [pivotRound, abs_mul, abs_mul, abs_of_nonneg h.1]
  calc
    _ ≤ (1 : ℚ) * 1 * 1 := by gcongr <;> first | exact h.1 | exact h.2 | apply hs
    _ = 1 := by norm_num

private theorem rat_cast_sign (q : ℚ) : ((sign q : ℚ) : ℝ) = (sign (q : ℝ) : ℝ) := by
  rcases lt_trichotomy q 0 with h | rfl | h
  · have hh : (q : ℝ) < 0 := by exact_mod_cast h
    simp [sign_neg h, sign_neg hh]
  · simp
  · have hh : 0 < (q : ℝ) := by exact_mod_cast h
    simp [sign_pos h, sign_pos hh]

/-- A maximizing nonzero coordinate realizes the sup norm of the priced minor row. -/
theorem norm_pricedMinorRow_of_max {n : ℕ} (raw f price : Fin n → ℝ) (p : Fin n)
    (hp : raw p ≠ 0) (hm : ∀ j, raw j ≠ 0 → f j - price j ≤ f p - price p) :
    ‖pricedMinorRow raw f price‖ = 2 ^ (f p - price p) := by
  have mag (j : Fin n) (hj : raw j ≠ 0) :
      ‖pricedMinorRow raw f price j‖ = (2 : ℝ) ^ (f j - price j) := by
    rcases lt_or_gt_of_ne hj with h | h <;>
      simp [pricedMinorRow, sign_neg, sign_pos, h, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (Real.rpow_nonneg (by norm_num) _)).2
    intro j
    by_cases hj : raw j = 0
    · simp [pricedMinorRow, hj, Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    · rw [mag j hj]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (hm j hj)
  · rw [← mag p hp]
    exact norm_le_pi_norm _ p

/-- The rational rounded row approximates the actual sign-oriented, sup-normalized row,
including every zero coordinate. -/
theorem pivotRound_error {n : ℕ} (raw f price : Fin n → ℚ) (p : Fin n) (B : ℕ)
    (hp : raw p ≠ 0) (hm : ∀ j, raw j ≠ 0 → f j - price j ≤ f p - price p) (j : Fin n) :
    |(pivotRound raw f price p B j : ℝ) - (sign ((raw p : ℚ) : ℝ) : ℝ) *
      normalizedMinorRow (fun u => (raw u : ℝ)) (fun u => (f u : ℝ))
        (fun u => (price u : ℝ)) j| ≤ (1 / 2 : ℝ) ^ B := by
  have hn := norm_pricedMinorRow_of_max (fun u => (raw u : ℝ)) (fun u => (f u : ℝ))
    (fun u => (price u : ℝ)) p (by exact_mod_cast hp) (by
      intro u hu
      exact_mod_cast hm u (by exact_mod_cast hu))
  by_cases hj : raw j = 0
  · simp [pivotRound, normalizedMinorRow, pricedMinorRow, hj]
  · let θ := (f j - price j) - (f p - price p)
    have hθ := roundedPower_error (show θ ≤ 0 from sub_nonpos.mpr (hm j hj)) B
    have hs (v : SignType) : |(v : ℝ)| ≤ 1 := by cases v <;> norm_num
    have he : (2 : ℝ) ^ (θ : ℝ) =
        (2 : ℝ)^((f j : ℝ) - (price j : ℝ)) / (2 : ℝ)^((f p : ℝ) - (price p : ℝ)) := by
      simp [θ, Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
    rw [pivotRound, Rat.cast_mul, Rat.cast_mul, rat_cast_sign, rat_cast_sign, normalizedMinorRow, hn,
      pricedMinorRow]
    change |(sign ((raw p : ℚ) : ℝ) : ℝ) * (sign ((raw j : ℚ) : ℝ) : ℝ) * (roundedPower θ B : ℝ) - _| ≤ _
    have hx : (2 : ℝ)^((f p : ℝ) - (price p : ℝ)) ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
    calc
      _ = |(sign ((raw p : ℚ) : ℝ) : ℝ)| * |(sign ((raw j : ℚ) : ℝ) : ℝ)| *
          |(roundedPower θ B : ℝ) - (2 : ℝ) ^ (θ : ℝ)| := by
        rw [← abs_mul, ← abs_mul, he, div_eq_mul_inv]
        congr 1; ring
      _ ≤ 1 * 1 * ((1 / 2 : ℝ) ^ B) := by gcongr <;> apply hs
      _ = _ := by ring

end Geometry
end LinearProgramming
end Optimization
end OAI

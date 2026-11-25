import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic

/-! # Rational square roots and normalization of local table entries

The local two-coordinate decomposition divides each entry of a Walsh-rotated
pair by its modulus. Table preparation can do this with integer square root
and rational division, with a constant loss in precision on the modulus
range furnished by the decomposition.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhaseTable

/-- Binary approximation to the square root, by flooring the scaled radicand
and taking the integer square root. -/
def sqrtRat (p : ℕ) (q : ℚ) : ℚ :=
  (Nat.sqrt ⌊q * ((2 : ℚ) ^ p) ^ 2⌋₊ : ℚ) / 2 ^ p

theorem sqrtRat_interval (p : ℕ) (q : ℚ) (hq : 0 ≤ q) :
    ((sqrtRat p q : ℚ) : ℝ) ≤ Real.sqrt (q : ℝ) ∧
    Real.sqrt (q : ℝ) < ((sqrtRat p q : ℚ) : ℝ) + 1 / (2 : ℝ) ^ p := by
  let n := ⌊q * ((2 : ℚ) ^ p) ^ 2⌋₊
  let s : ℝ := 2 ^ p
  have hs : 0 < s := by dsimp [s]; positivity
  have hnq : (n : ℚ) ≤ q * ((2 : ℚ) ^ p) ^ 2 := Nat.floor_le (by positivity)
  have hqn : q * ((2 : ℚ) ^ p) ^ 2 < (n : ℚ) + 1 := Nat.lt_floor_add_one _
  have hn : (n : ℝ) ≤ (q : ℝ) * s ^ 2 := by
    simpa [s] using (Rat.cast_le (K := ℝ)).mpr hnq
  have hn' : (q : ℝ) * s ^ 2 < (n : ℝ) + 1 := by
    simpa [s] using (Rat.cast_lt (K := ℝ)).mpr hqn
  have hl : (n.sqrt : ℝ) ^ 2 ≤ (n : ℝ) := by exact_mod_cast Nat.sqrt_le' n
  have hu : (n : ℝ) + 1 ≤ ((n.sqrt : ℝ) + 1) ^ 2 := by
    exact_mod_cast (Nat.lt_succ_sqrt' n)
  have hr : (Real.sqrt (q : ℝ) * s) ^ 2 = (q : ℝ) * s ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by exact_mod_cast hq)]
  have hnon : 0 ≤ Real.sqrt (q : ℝ) * s := by positivity
  have hl' : (n.sqrt : ℝ) ≤ Real.sqrt (q : ℝ) * s :=
    (sq_le_sq₀ (by positivity) hnon).mp (by rw [hr]; exact hl.trans hn)
  have hu' : Real.sqrt (q : ℝ) * s < (n.sqrt : ℝ) + 1 :=
    (sq_lt_sq₀ hnon (by positivity)).mp (by rw [hr]; exact hn'.trans_le hu)
  have he : ((sqrtRat p q : ℚ) : ℝ) = (n.sqrt : ℝ) / s := by
    simp [sqrtRat, n, s]
  rw [he, ← add_div]
  exact ⟨(div_le_iff₀ hs).mpr hl', (lt_div_iff₀ hs).mpr hu'⟩

/-- The computed real and imaginary parts of a local coefficient. -/
def toComplex (q : ℚ × ℚ) : ℂ := ⟨q.1, q.2⟩

/-- Square of the complex modulus, obtained by rational operations. -/
def normSqRat (q : ℚ × ℚ) : ℚ := q.1 ^ 2 + q.2 ^ 2

theorem normSqRat_cast (q : ℚ × ℚ) :
    (normSqRat q : ℝ) = ‖toComplex q‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [normSqRat, toComplex, pow_two]

/-- Approximation to the modulus of a rational complex number. -/
def modulus (p : ℕ) (q : ℚ × ℚ) : ℚ := sqrtRat p (normSqRat q)

/-- Approximation to the phase, using the computed modulus as denominator. -/
def unitPhase (p : ℕ) (q : ℚ × ℚ) : ℚ × ℚ :=
  (q.1 / modulus p q, q.2 / modulus p q)

theorem modulus_interval (p : ℕ) (q : ℚ × ℚ) :
    (modulus p q : ℝ) ≤ ‖toComplex q‖ ∧
    ‖toComplex q‖ < (modulus p q : ℝ) + 1 / (2 : ℝ) ^ p := by
  have h := sqrtRat_interval p (normSqRat q) (by unfold normSqRat; positivity)
  rwa [normSqRat_cast, Real.sqrt_sq (norm_nonneg _)] at h

private theorem unitPhase_cast (p : ℕ) (q : ℚ × ℚ) :
    toComplex (unitPhase p q) = toComplex q / ((modulus p q : ℝ) : ℂ) := by
  apply Complex.ext
  · simp [unitPhase, toComplex]
  · simp [unitPhase, toComplex]

/-- Error of rational phase normalization in the uniformly conditioned range
of the pair decomposition. Both the numerator and its computed modulus are
allowed to differ from the ideal values. -/
theorem unitPhase_error (p : ℕ) (q : ℚ × ℚ) (z : ℂ) (ε : ℝ)
    (hz : 1 / 5 ≤ ‖z‖) (hq : ‖toComplex q - z‖ ≤ ε)
    (hε : ε ≤ 1 / 40) (hp : 1 / (2 : ℝ) ^ p ≤ 1 / 40) :
    ‖toComplex (unitPhase p q) - z / (‖z‖ : ℂ)‖ ≤ 10 * (2 * ε + 1 / (2 : ℝ) ^ p) := by
  let r : ℝ := modulus p q
  let γ := z / (‖z‖ : ℂ)
  obtain ⟨hlo, hhi⟩ := modulus_interval p q
  change r ≤ ‖toComplex q‖ at hlo
  change ‖toComplex q‖ < r + _ at hhi
  have hnorm := abs_norm_sub_norm_le (toComplex q) z
  have habs := abs_le.mp (hnorm.trans hq)
  have hr : 1 / 10 ≤ r := by linarith
  have hrpos : 0 < r := by linarith
  have hzpos : 0 < ‖z‖ := by linarith
  have hγ : ‖γ‖ = 1 := by
    simp [γ, div_self hzpos.ne']
  have he : (‖z‖ : ℂ) * γ = z := by
    dsimp [γ]
    field_simp [show (‖z‖ : ℂ) ≠ 0 by exact_mod_cast hzpos.ne']
  have hmod : |‖z‖ - r| ≤ ε + 1 / (2 : ℝ) ^ p := by
    rw [abs_le]
    constructor <;> linarith [one_div_pos.mpr (show 0 < (2 : ℝ) ^ p by positivity)]
  have hnum :
      ‖toComplex q - (r : ℂ) * γ‖ ≤ 2 * ε + 1 / (2 : ℝ) ^ p := calc
    ‖toComplex q - (r : ℂ) * γ‖ = ‖(toComplex q - z) + ((‖z‖ - r : ℝ) : ℂ) * γ‖ := by
      congr 1
      push_cast
      linear_combination -he
    _ ≤ ‖toComplex q - z‖ + ‖((‖z‖ - r : ℝ) : ℂ) * γ‖ := norm_add_le _ _
    _ ≤ _ := by
      rw [norm_mul, hγ, mul_one, Complex.norm_real, Real.norm_eq_abs]
      linarith
  rw [unitPhase_cast]
  change ‖toComplex q / (r : ℂ) - γ‖ ≤ _
  rw [show toComplex q / (r : ℂ) - γ = (toComplex q - (r : ℂ) * γ) / (r : ℂ) by
    field_simp [show (r : ℂ) ≠ 0 by exact_mod_cast hrpos.ne'], norm_div,
    Complex.norm_of_nonneg hrpos.le, div_le_iff₀ hrpos]
  have hnon : 0 ≤ 2 * ε + 1 / (2 : ℝ) ^ p := by
    have := (norm_nonneg _).trans hq
    positivity
  nlinarith [mul_le_mul_of_nonneg_left hr hnon]

end PhaseTable

end NearSquareRoot
end Computability
end OAI

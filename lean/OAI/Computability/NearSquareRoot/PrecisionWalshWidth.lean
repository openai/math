import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-! # Widths in the fixed-point Walsh execution

Once the number of array operations and the gains from individual arrays have
polynomial bounds, their contribution to the required word width is absorbed
by a fixed number of bits per address bit.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

open Filter

section

/-- A common envelope for operation counts and gains is eventually below the
array length. -/
theorem eventually_polynomial_le_array_length (C : ℝ) (hC : 0 ≤ C) (d : ℕ) :
    ∀ᶠ k : ℕ in atTop, C * (1 + (k : ℝ))^d ≤ (2 : ℝ)^k := by
  have h₀ := isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) d (by norm_num : 1 < (2 : ℝ))
  have h := (h₀.const_mul_left (C * 2^d)).bound zero_lt_one
  filter_upwards [h, eventually_ge_atTop 1] with k hk hk₁
  have h1 : 1 ≤ (k : ℝ) := by exact_mod_cast hk₁
  calc
    C * (1 + (k : ℝ))^d ≤ C * (2 * (k : ℝ))^d := by gcongr; linarith
    _ = (C * 2^d) * (k : ℝ)^d := by ring
    _ ≤ (2 : ℝ)^k := by simpa [Real.norm_eq_abs, abs_of_nonneg, hC] using hk

/-- Include the finite initial range when absorbing a polynomial setup clock
into the length of a binary array. -/
theorem polynomial_le_multiple_array_length (d : ℕ) :
    ∃ C : ℕ, ∀ k : ℕ, (k+1)^d ≤ C*2^k := by
  obtain ⟨K, hK⟩ := eventually_atTop.mp
    (eventually_polynomial_le_array_length 1 (by norm_num) d)
  refine ⟨(K+1)^d, fun k => ?_⟩
  by_cases hk : K ≤ k
  · have h := hK k hk
    simp only [one_mul, add_comm (1 : ℝ)] at h
    exact (show (k+1)^d ≤ (2 : ℕ)^k by exact_mod_cast h).trans
      (Nat.le_mul_of_pos_left _ (by positivity))
  · have h : (k+1)^d ≤ (K+1)^d := Nat.pow_le_pow_left (by omega) _
    exact h.trans (Nat.le_mul_of_pos_right _ (by positivity))

/-- With input norm at most `2^(L*k)`, a polynomial gain gives room for
intermediate vectors. At precision `p ≥ (L+D+7)*k`, the sum of the propagated
faults is at most `2^(-D*k)`, even for operands up to the larger norm guard.
Here `C*(1+k)^d` bounds both the number of faults and each fault's gain. -/
theorem eventually_walsh_width_bounds (C : ℝ) (hC : 0 ≤ C) (d L D : ℕ) :
    ∀ᶠ k : ℕ in atTop,
      C * (1 + (k : ℝ))^d * 2^(L*k) ≤ (2 : ℝ)^((L+1)*k) ∧
      (2 : ℝ)^((L+1)*k) + ((2 : ℝ)^(D*k))⁻¹ ≤ (2 : ℝ)^((L+2)*k) ∧
      ∀ p : ℕ, (L+D+7)*k ≤ p →
        (C * (1 + (k : ℝ))^d)^2 * C * Real.sqrt (2^k) * ((2 : ℝ)^p)⁻¹ *
          (1 + 2^((L+2)*k)) ≤ ((2 : ℝ)^(D*k))⁻¹ := by
  filter_upwards [eventually_polynomial_le_array_length C hC d, eventually_ge_atTop 1]
    with k hP hk
  let q : ℝ := 2^k
  let P : ℝ := C * (1 + (k : ℝ))^d
  change P ≤ q at hP
  have hq : 2 ≤ q := by
    calc
      (2 : ℝ) = 2^1 := by norm_num
      _ ≤ 2^k := pow_le_pow_right₀ (by norm_num) hk
  have hq₁ : 1 ≤ q := by linarith
  have hCP : C ≤ P := le_mul_of_one_le_right hC (one_le_pow₀ (by simp : 1 ≤ 1 + (k : ℝ)))
  have h1 (n : ℕ) : (2 : ℝ)^(n*k) = q^n := by rw [Nat.mul_comm, pow_mul]
  have hplus (n : ℕ) : 1 + q^n ≤ q^n*q := by
    have hpow := one_le_pow₀ hq₁ (n := n)
    nlinarith [mul_le_mul_of_nonneg_right hq (zero_le_one.trans hpow)]
  constructor
  · rw [h1, h1, pow_succ]
    exact ((mul_le_mul_of_nonneg_right hP (pow_nonneg (by linarith) _)).trans_eq (mul_comm _ _))
  constructor
  · rw [h1, h1, h1, show L+2 = (L+1)+1 by omega, pow_succ q (L+1)]
    have hi := inv_le_one_of_one_le₀ (one_le_pow₀ hq₁ (n := D))
    linarith [hplus (L+1)]
  intro p hp
  change P^2 * C * Real.sqrt q * ((2 : ℝ)^p)⁻¹ * (1 + 2^((L+2)*k)) ≤ _
  rw [h1, h1]
  have hnum : P^2 * C * Real.sqrt q * (1 + q^(L+2)) ≤ q^(L+7) := by
    calc
      P^2 * C * Real.sqrt q * (1 + q^(L+2)) ≤ q^2 * q * q * (q^(L+2)*q) := by
        gcongr
        · exact hCP.trans hP
        · exact Real.sqrt_le_self_iff.mpr (.inr hq₁)
        · exact hplus _
      _ = q^(L+7) := by ring
  calc
    _ = (P^2 * C * Real.sqrt q * (1 + q^(L+2))) * ((2 : ℝ)^p)⁻¹ := by ring
    _ ≤ q^(L+7) * ((2 : ℝ)^((L+D+7)*k))⁻¹ := by
      exact mul_le_mul hnum (inv_anti₀ (by positivity)
        (pow_le_pow_right₀ (by norm_num) hp)) (by positivity) (pow_nonneg (zero_le_one.trans hq₁) _)
    _ = (q^D)⁻¹ := by
      rw [h1, show L+D+7 = L+7+D by omega, pow_add q (L+7) D]
      have hqpos : 0 < q := by linarith
      field_simp

end

end NearSquareRoot
end Computability
end OAI

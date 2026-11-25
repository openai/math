import OAI.NumberTheory.JointDickman.Arithmetic.TotientWeightedKernel
import OAI.NumberTheory.JointDickman.Amplification.GcdReciprocalMean

/-! # The harmonic sum of reciprocal totients

In the divisor expansion of the totient correction, writing `h = d * k`
leaves a reciprocal square in `d` and a harmonic sum in `k`.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Finset

/-- The sum of `1 / φ(h)` up to `H` grows at most logarithmically. -/
theorem exists_reciprocal_totient_sum_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℕ, 1 ≤ H →
      (∑ h ∈ Icc 1 H, (h.totient : ℝ)⁻¹) ≤ C * (1 + Real.log H) := by
  refine ⟨Real.exp 2 * 2, by positivity, ?_⟩
  intro H hH
  have hint : Icc 1 H = Ioc 0 H := by ext x; simp [Nat.lt_iff_add_one_le]
  rw [hint]
  have hsum := JointDickman.totient_weighted_sum_le_divisor_sum (fun k => 1 / (k : ℝ))
    (fun k => by positivity) H
  have hleft (h : ℕ) (hh : h ∈ Ioc 0 H) :
      (h : ℝ) / h.totient * (1 / (h : ℝ)) = (h.totient : ℝ)⁻¹ := by
    have hh' : (h : ℝ) ≠ 0 := by exact_mod_cast (mem_Ioc.mp hh).1.ne'
    field_simp
  have hinner (d : ℕ) :
      (∑ k ∈ Ioc 0 (H / d), 1 / (k : ℝ)) ≤ 1 + Real.log H := by
    refine le_trans (sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity))
      (JointDickman.reciprocal_initial_sum H)
    exact Ioc_subset_Ioc le_rfl (Nat.div_le_self H d)
  have hterm (d : ℕ) :
      1 / (d : ℝ) * ∑ k ∈ Ioc 0 (H / d), 1 / ((d*k : ℕ) : ℝ) ≤
        1 / (d : ℝ)^2 * (1 + Real.log H) := by
    simp only [Nat.cast_mul, one_div, mul_inv]
    rw [← mul_sum, ← mul_assoc, ← mul_inv, ← sq]
    exact mul_le_mul_of_nonneg_left (by simpa only [one_div] using hinner d) (by positivity)
  rw [sum_congr rfl hleft] at hsum
  calc
    _ ≤ _ := hsum
    _ ≤ Real.exp 2 * ∑ d ∈ Ioc 0 H, 1 / (d : ℝ)^2 * (1 + Real.log H) :=
      mul_le_mul_of_nonneg_left (sum_le_sum fun d _ => hterm d) (Real.exp_pos _).le
    _ = Real.exp 2 * ((∑ d ∈ Ioc 0 H, 1 / (d : ℝ)^2) * (1 + Real.log H)) := by rw [sum_mul]
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (JointDickman.reciprocal_square_initial_sum H)
        (by linarith [Real.log_nonneg (show (1 : ℝ) ≤ H by exact_mod_cast hH)]))
        (Real.exp_pos _).le

end FiniteFourier
end LinearAlgebra
end OAI

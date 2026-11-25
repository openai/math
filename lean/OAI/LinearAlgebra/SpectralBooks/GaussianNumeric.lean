import OAI.LinearAlgebra.SpectralBooks.GaussianTest
import OAI.LinearAlgebra.SpectralBooks.StudentTwo
import Mathlib.Analysis.Real.Pi.Bounds

/-! # A strict rational lower bound for the Gaussian square exponent -/

namespace OAI
namespace LinearAlgebra.SpectralBooks

open Filter MeasureTheory ProbabilityTheory Set Real
open scoped Topology
open private normalTail_deriv from OAI.LinearAlgebra.SpectralBooks.StudentTwo

private theorem exp_neg_quadratic_upper (x : ℝ) (hx : 0 ≤ x) :
    exp (-x) ≤ 1 - x + x ^ 2 / 2 := by
  rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
  have factor : 0 ≤ 1 - x + x ^ 2 / 2 := by nlinarith [sq_nonneg (x - 1)]
  have lower := mul_le_mul_of_nonneg_right (Real.quadratic_le_exp_of_nonneg hx) factor
  nlinarith [sq_nonneg (x ^ 2)]

private noncomputable def primitive (x : ℝ) := x - x ^ 3 / 6 + x ^ 5 / 40

private theorem primitive_deriv (x : ℝ) :
    HasDerivAt primitive (1 - x ^ 2 / 2 + x ^ 4 / 8) x := by
  convert! (((hasDerivAt_id x).sub (((hasDerivAt_id x).pow 3).div_const 6)).add
    (((hasDerivAt_id x).pow 5).div_const 40)) using 1
  simp
  ring

/-- Integrating the upper bound for the standard normal density gives a
strictly positive rational margin at 31/72. -/
private theorem normalTail_at_test : (1 : ℝ) / 3 < normalTail (31 / 72) := by
  let a : ℝ := (√(2 * π))⁻¹
  have apos : 0 < a := by dsimp [a]; positivity
  let g := fun x : ℝ => normalTail x + a * primitive x
  have dg (x : ℝ) : HasDerivAt g
      (-gaussianPDFReal 0 1 x + a * (1 - x ^ 2 / 2 + x ^ 4 / 8)) x :=
    (normalTail_deriv x).add ((primitive_deriv x).const_mul a)
  have inc : Monotone g := by
    apply monotone_of_deriv_nonneg (fun x => (dg x).differentiableAt)
    intro x
    rw [(dg x).deriv]
    have h := exp_neg_quadratic_upper (x ^ 2 / 2) (by positivity)
    have bound : exp (-(x ^ 2) / 2) ≤ 1 - x ^ 2 / 2 + x ^ 4 / 8 := by
      rw [show -(x ^ 2) / 2 = -(x ^ 2 / 2) by ring]
      exact h.trans_eq (by ring)
    have pdf : gaussianPDFReal 0 1 x = a * exp (-(x ^ 2) / 2) := by simp [gaussianPDFReal, a]
    rw [pdf]
    linarith [mul_le_mul_of_nonneg_left bound apos.le]
  have at_q := inc (show (0 : ℝ) ≤ 31 / 72 by norm_num)
  change normalTail 0 + a * primitive 0 ≤ normalTail (31 / 72) + a * primitive (31 / 72) at at_q
  rw [normalTail_zero] at at_q
  have small : 6 * primitive (31 / 72) < √(2 * π) := by
    have square : (6 * primitive (31 / 72)) ^ 2 < (157 : ℝ) / 25 := by norm_num [primitive]
    nlinarith [Real.pi_gt_d2, Real.sq_sqrt (show 0 ≤ 2 * π by positivity), Real.sqrt_nonneg (2 * π)]
  have paid : a * primitive (31 / 72) < 1 / 6 := by
    dsimp only [a]
    rw [← div_eq_inv_mul, div_lt_div_iff₀ (by positivity) (by norm_num)]
    linarith
  norm_num [primitive] at at_q paid ⊢
  linarith

private theorem test_le_quantile : (31 : ℝ) / 72 ≤ stdNormalQuantile (2 / 3) := by
  let μ := gaussianReal 0 1
  have ultimately := (tendsto_cdf_atTop μ).eventually (lt_mem_nhds (show (2 : ℝ) / 3 < 1 by norm_num))
  obtain ⟨z, hz⟩ := ultimately.exists
  have test := normalTail_at_test
  rw [normalTail_eq_one_sub_cdf] at test
  apply le_csInf (show {x : ℝ | 2 / 3 ≤ cdf μ x}.Nonempty from ⟨z, hz.le⟩)
  intro x hx
  change 2 / 3 ≤ cdf μ x at hx
  by_contra! h
  have order := monotone_cdf μ h.le
  change cdf (gaussianReal 0 1) x ≤ cdf (gaussianReal 0 1) (31 / 72) at order
  dsimp only [μ] at hx
  linarith

/-- The Gaussian lower-bound constant strictly exceeds the rational number 1097/500. -/
theorem gaussianSquareExponent_gt_2194 :
    (1097 : ℝ) / 500 < 2 * exp (stdNormalQuantile (2 / 3) ^ 2 / 2) := by
  have qle := test_le_quantile
  let t : ℝ := ((31 : ℝ) / 72) ^ 2 / 2
  have bound := Real.sum_le_exp_of_nonneg (show 0 ≤ t by dsimp [t]; positivity) 4
  have numeric : (1097 : ℝ) / 500 < 2 * exp t := by
    norm_num [Finset.sum_range_succ, t, Nat.factorial] at bound ⊢
    linarith
  have sq := sq_le_sq' (show -stdNormalQuantile (2 / 3) ≤ (31 : ℝ) / 72 by linarith) qle
  exact numeric.trans_le (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (by dsimp [t]; linarith)) (by norm_num))

end LinearAlgebra.SpectralBooks

end OAI

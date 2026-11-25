import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Tactic

/-! # Gaussian radial integrals

The chi density in positive integral dimension, its first moment, the effect of
size biasing by the radius, and its squared-radius Laplace transform.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

open Set MeasureTheory

section

/-- The unnormalized chi density with Gaussian decay coefficient `b`. -/
def chiKernel (q : ℕ) (b : ℝ) : ℝ → ℝ :=
  (Ioi 0).indicator (fun h : ℝ ↦ h ^ ((q : ℝ) - 1) * Real.exp (-b * h ^ 2))

/-- The integral of the unnormalized standard chi density. -/
def chiNormalizer (q : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ (-(q : ℝ) / 2) * (1 / 2) * Real.Gamma ((q : ℝ) / 2)

/-- Density of the chi distribution with `q` degrees of freedom. -/
def chiDensity (q : ℕ) (h : ℝ) : ℝ := (chiNormalizer q)⁻¹ * chiKernel q (1 / 2) h

/-- The mean radius, as a ratio of consecutive radial normalization factors. -/
def chiMean (q : ℕ) : ℝ := chiNormalizer (q + 1) / chiNormalizer q

lemma chiNormalizer_pos {q : ℕ} (hq : 0 < q) : 0 < chiNormalizer q := by
  unfold chiNormalizer
  have h : 0 < (q : ℝ) / 2 := by positivity
  exact mul_pos (mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (by norm_num)) (Real.Gamma_pos_of_pos h)

lemma chiMean_pos {q : ℕ} (hq : 0 < q) : 0 < chiMean q :=
  div_pos (chiNormalizer_pos (Nat.succ_pos _)) (chiNormalizer_pos hq)

lemma measurable_chiKernel (q : ℕ) (b : ℝ) : Measurable (chiKernel q b) := by
  unfold chiKernel
  apply Measurable.indicator _ measurableSet_Ioi
  fun_prop

lemma measurable_chiDensity (q : ℕ) : Measurable (chiDensity q) :=
  measurable_const.mul (measurable_chiKernel q _)

lemma chiKernel_nonneg (q : ℕ) (b h : ℝ) : 0 ≤ chiKernel q b h := by
  by_cases hh : 0 < h
  · simp only [chiKernel, indicator_of_mem (mem_Ioi.mpr hh)]
    positivity
  · simp [chiKernel, hh]

lemma chiDensity_nonneg {q : ℕ} (hq : 0 < q) (h : ℝ) : 0 ≤ chiDensity q h :=
  mul_nonneg (inv_nonneg.mpr (chiNormalizer_pos hq).le) (chiKernel_nonneg ..)

lemma integrable_chiKernel {q : ℕ} (hq : 0 < q) {b : ℝ} (hb : 0 < b) :
    Integrable (chiKernel q b) := by
  unfold chiKernel
  rw [integrable_indicator_iff measurableSet_Ioi]
  apply integrableOn_rpow_mul_exp_neg_mul_sq hb
  have : 0 < (q : ℝ) := by exact_mod_cast hq
  linarith

lemma integral_chiKernel {q : ℕ} (hq : 0 < q) {b : ℝ} (hb : 0 < b) :
    ∫ h, chiKernel q b h = b ^ (-(q : ℝ) / 2) * (1 / 2) * Real.Gamma ((q : ℝ) / 2) := by
  unfold chiKernel
  rw [integral_indicator measurableSet_Ioi]
  have hq' : 0 < (q : ℝ) := by exact_mod_cast hq
  simpa only [Real.rpow_two, sub_add_cancel] using
    (integral_rpow_mul_exp_neg_mul_rpow (p := (2 : ℝ)) (q := (q : ℝ) - 1)
      (by norm_num) (by linarith) hb)

lemma integrable_chiDensity {q : ℕ} (hq : 0 < q) : Integrable (chiDensity q) :=
  (integrable_chiKernel hq (by norm_num : 0 < (1/2 : ℝ))).const_mul _

lemma integral_chiDensity {q : ℕ} (hq : 0 < q) : ∫ h, chiDensity q h = 1 := by
  unfold chiDensity
  rw [integral_const_mul, integral_chiKernel hq (by norm_num)]
  exact inv_mul_cancel₀ (chiNormalizer_pos hq).ne'

/-- Weighting by the radius changes the radial dimension from `q` to `q + 1`. -/
theorem chiDensity_sizeBias {q : ℕ} (hq : 0 < q) (h : ℝ) :
    h * chiDensity q h = chiMean q * chiDensity (q + 1) h := by
  by_cases hh : 0 < h
  · simp only [chiDensity, chiKernel, indicator_of_mem (mem_Ioi.mpr hh), Nat.cast_add_one,
      add_sub_cancel_right, chiMean]
    rw [Real.rpow_sub_one hh.ne']
    field_simp [hh.ne', (chiNormalizer_pos hq).ne', (chiNormalizer_pos (Nat.succ_pos q)).ne']
  · simp [chiDensity, chiKernel, hh]

lemma integrable_mul_chiDensity {q : ℕ} (hq : 0 < q) :
    Integrable (fun h ↦ h * chiDensity q h) := by
  simp_rw [chiDensity_sizeBias hq]
  exact (integrable_chiDensity (Nat.succ_pos q)).const_mul _

lemma integral_mul_chiDensity {q : ℕ} (hq : 0 < q) : ∫ h, h * chiDensity q h = chiMean q := by
  simp_rw [chiDensity_sizeBias hq]
  rw [integral_const_mul, integral_chiDensity (Nat.succ_pos q), mul_one]

private lemma chiDensity_mul_exp (q : ℕ) (t h : ℝ) :
    chiDensity q h * Real.exp (-(t * h ^ 2) / 2) =
      (chiNormalizer q)⁻¹ * chiKernel q ((1 + t) * (1 / 2)) h := by
  by_cases hh : 0 < h
  · simp only [chiDensity, chiKernel, indicator_of_mem (mem_Ioi.mpr hh), mul_assoc, ← Real.exp_add]
    congr 3
    ring
  · simp [chiDensity, chiKernel, hh]

lemma integrable_chiDensity_laplace {q : ℕ} (hq : 0 < q) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun h ↦ chiDensity q h * Real.exp (-(t * h ^ 2) / 2)) := by
  simp_rw [chiDensity_mul_exp]
  exact (integrable_chiKernel hq (by positivity)).const_mul _

/-- The Laplace transform of half the squared standard Gaussian radius. -/
theorem integral_chiDensity_laplace {q : ℕ} (hq : 0 < q) {t : ℝ} (ht : 0 ≤ t) :
    ∫ h : ℝ, chiDensity q h * Real.exp (-(t * h ^ 2) / 2) = (1 + t) ^ (-(q : ℝ) / 2) := by
  simp_rw [chiDensity_mul_exp]
  rw [integral_const_mul, integral_chiKernel hq (by positivity),
    Real.mul_rpow (by positivity) (by norm_num)]
  change (chiNormalizer q)⁻¹ * _ = _
  rw [mul_assoc ((1 + t) ^ _), mul_assoc ((1 + t) ^ _)]
  change (chiNormalizer q)⁻¹ * (_ * chiNormalizer q) = _
  field_simp [(chiNormalizer_pos hq).ne']

/-- The polar-coordinate radial integral, expressed in terms of the normalized chi law. -/
theorem integral_chiKernel_nat_eq {q : ℕ} (hq : 0 < q) (f : ℝ → ℝ) :
    (∫ r in Ioi (0 : ℝ), r ^ (q - 1) * Real.exp (-r ^ 2 / 2) * f r) =
      chiNormalizer q * ∫ r, chiDensity q r * f r := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with r
  by_cases hr : 0 < r
  · simp only [indicator_of_mem (mem_Ioi.mpr hr), chiDensity, chiKernel]
    have hcast : ((q - 1 : ℕ) : ℝ) = q - 1 := by rw [Nat.cast_sub hq, Nat.cast_one]
    rw [← hcast, Real.rpow_natCast]
    rw [show -(1 / 2 : ℝ) * r ^ 2 = -r ^ 2 / 2 by ring]
    field_simp [(chiNormalizer_pos hq).ne']
  · simp [chiDensity, chiKernel, hr]

end

end

end SpectralBooks
end LinearAlgebra
end OAI

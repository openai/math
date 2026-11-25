import OAI.LinearAlgebra.SpectralBooks.Dimension
import OAI.LinearAlgebra.SpectralBooks.Rank
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

namespace OAI
/-! # The upper tail for two degrees of freedom -/

namespace LinearAlgebra.SpectralBooks

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped Topology

private theorem normalTail_integral (s : ℝ) :
    normalTail s = ∫ x in Ioi s, gaussianPDFReal 0 1 x := by
  rw [normalTail, measureReal_def, gaussianReal_apply_eq_integral 0 one_ne_zero,
    ENNReal.toReal_ofReal (integral_nonneg (gaussianPDFReal_nonneg 0 1))]

private theorem normalTail_deriv (s : ℝ) :
    HasDerivAt normalTail (-gaussianPDFReal 0 1 s) s := by
  have hc : Continuous (gaussianPDFReal 0 1) := by
    rw [gaussianPDFReal_def]
    fun_prop
  have h := intervalIntegral.integral_hasDerivAt_left (hc.intervalIntegrable s 0)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  apply (h.add_const (∫ x in Ioi 0, gaussianPDFReal 0 1 x)).congr_of_eventuallyEq
  filter_upwards with t
  rw [normalTail_integral, intervalIntegral.integral_interval_add_Ioi
    (integrable_gaussianPDFReal 0 1).integrableOn (integrable_gaussianPDFReal 0 1).integrableOn]

/-- The radial integral for two Gaussian coordinates, with normal threshold `c * h`. -/
theorem integral_rayleigh_normalTail (c : ℝ) (hc : 0 ≤ c) :
    (∫ h : ℝ in Ioi 0, h * exp (-(h ^ 2) / 2) * normalTail (c * h)) =
      (1 - c / √(1 + c ^ 2)) / 2 := by
  let b : ℝ := (1 + c ^ 2) / 2
  have hb : 0 < b := by dsimp [b]; positivity
  let f := fun h : ℝ ↦ exp (-(h ^ 2) / 2) * normalTail (c * h)
  let g := fun h : ℝ ↦ h * exp (-(h ^ 2) / 2) * normalTail (c * h)
  let k := fun h : ℝ ↦ c / √(2 * π) * exp (-b * h ^ 2)
  have hder (h : ℝ) : HasDerivAt f (-(g h + k h)) h := by
    have h₁ : HasDerivAt (fun t : ℝ ↦ exp (-(t ^ 2) / 2)) (-h * exp (-(h ^ 2) / 2)) h := by
      convert! (((hasDerivAt_pow 2 h).neg.div_const 2).exp) using 1
      simp
      ring
    have h₂ := (normalTail_deriv (c * h)).comp h ((hasDerivAt_id h).const_mul c)
    convert! h₁.mul h₂ using 1
    simp only [Function.comp_apply, g, k, b, gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
    rw [show -((1 + c ^ 2) / 2) * h ^ 2 = -(h ^ 2) / 2 + -((c * h) ^ 2) / 2 by ring, Real.exp_add]
    ring
  have hlim : Tendsto f atTop (𝓝 0) := by
    have hh : Tendsto (fun h : ℝ ↦ exp (-(h ^ 2) / 2)) atTop (𝓝 0) := by
      simpa [Function.comp_def, neg_div] using Real.tendsto_exp_neg_atTop_nhds_zero.comp
        ((tendsto_pow_atTop (α := ℝ) (n := 2) (by decide)).atTop_div_const (by norm_num : (0 : ℝ) < 2))
    apply squeeze_zero (fun h ↦ mul_nonneg (Real.exp_pos _).le (normalTail_nonneg _)) _ hh
    intro h
    exact mul_le_of_le_one_right (Real.exp_pos _).le (normalTail_le_one _)
  have hgpos (h : ℝ) (hh : 0 ≤ h) : 0 ≤ g h :=
    mul_nonneg (mul_nonneg hh (Real.exp_pos _).le) (normalTail_nonneg _)
  have hkpos (h : ℝ) : 0 ≤ k h := by dsimp [k]; positivity
  have hneg (h : ℝ) (hh : h ∈ Ioi 0) : -(g h + k h) ≤ 0 :=
    neg_nonpos.mpr (add_nonneg (hgpos _ hh.le) (hkpos _))
  have hi := integral_Ioi_of_hasDerivAt_of_nonpos' (fun h _ ↦ hder h) hneg hlim
  have hgk := integrableOn_Ioi_deriv_of_nonpos' (fun h _ ↦ hder h) hneg hlim
  have hk : IntegrableOn k (Ioi 0) := ((integrable_exp_neg_mul_sq hb).const_mul _).integrableOn
  have hg : IntegrableOn g (Ioi 0) := by
    have := hgk.neg.sub hk
    simpa [Pi.neg_def, Pi.sub_def] using this
  rw [integral_neg, integral_add hg hk] at hi
  have ik : (∫ h : ℝ in Ioi 0, k h) = c / √(1 + c ^ 2) / 2 := by
    dsimp [k]
    rw [integral_const_mul, integral_gaussian_Ioi]
    have hpi := Real.pi_pos
    have hb' : 0 < 1 + c ^ 2 := by positivity
    rw [show π / b = 2 * π / (1 + c ^ 2) by dsimp [b]; field_simp,
      Real.sqrt_div (by positivity)]
    field_simp
  simp [f, normalTail_zero, ik] at hi
  change (∫ h : ℝ in Ioi 0, g h) = _
  linarith

/-- Closed form of the Student tail with two degrees of freedom. -/
theorem studentTail_two {s : ℝ} (hs : 0 ≤ s) :
    studentTail 2 s = (1 - s / √(s ^ 2 + 2)) / 2 := by
  have hn : chiNormalizer 2 = 1 := by norm_num [chiNormalizer, Real.Gamma_one]
  have h2 : 0 < √(2 : ℝ) := by positivity
  let c := s / √2
  calc
    studentTail 2 s = ∫ h in Ioi 0, h * exp (-(h ^ 2) / 2) * normalTail (c * h) := by
      rw [studentTail, ← integral_indicator measurableSet_Ioi]
      apply integral_congr_ae
      filter_upwards with h
      by_cases hh : h ∈ Ioi 0
      · rw [indicator_of_mem hh, chiDensity, hn, inv_one, one_mul, chiKernel, indicator_of_mem hh]
        norm_num [c, div_eq_mul_inv, neg_mul, mul_comm, mul_assoc, mul_left_comm]
      · simp [chiDensity, chiKernel, hh]
    _ = (1 - c / √(1 + c ^ 2)) / 2 :=
      integral_rayleigh_normalTail c (div_nonneg hs h2.le)
    _ = _ := by
      have hsqrt : √(1 + c ^ 2) = √(s ^ 2 + 2) / √2 := by
        rw [← Real.sqrt_div (by positivity), Real.sqrt_inj (by positivity) (by positivity)]
        dsimp [c]
        rw [div_pow, Real.sq_sqrt (by norm_num)]
        ring
      rw [hsqrt]
      dsimp [c]
      field_simp

private theorem studentTail_two_load {L m : ℝ} (hm : 0 < m) (hmL : m ≤ L) :
    studentTail 2 (√(2 * ((L / m) ^ 2 - 1))) = (1 - √(L ^ 2 - m ^ 2) / L) / 2 := by
  have hL : 0 < L := lt_of_lt_of_le hm hmL
  have hr : 1 ≤ L / m := (one_le_div hm).mpr hmL
  have ha : 0 ≤ 2 * ((L / m) ^ 2 - 1) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hr) (by linarith : 0 ≤ L / m + 1)]
  have hb : 0 ≤ L ^ 2 - m ^ 2 := sub_nonneg.mpr (sq_le_sq' (by linarith) hmL)
  let a := √(2 * ((L / m) ^ 2 - 1))
  have ha' : a ^ 2 = 2 * ((L / m) ^ 2 - 1) := Real.sq_sqrt ha
  have heq : a / √(a ^ 2 + 2) = √(L ^ 2 - m ^ 2) / L := by
    apply (sq_eq_sq₀ (by dsimp [a]; positivity) (by positivity)).mp
    rw [div_pow, div_pow, Real.sq_sqrt (show 0 ≤ a ^ 2 + 2 by positivity), Real.sq_sqrt hb, ha']
    field_simp
    ring
  rw [studentTail_two (Real.sqrt_nonneg _), heq]

/-- In dimension two the Student inequality for three nonnegative loads is
equivalent to the finite rectangular radical test, including zero loads. -/
theorem studentTail_two_sum_iff {L : ℝ} (m : Fin 3 → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hmL : ∀ i, m i ≤ L) :
    (∑ i with 0 < m i, studentTail 2 (√(2 * ((L / m i) ^ 2 - 1)))) ≤ 1 ↔
      L ≤ ∑ i, √(L ^ 2 - (m i) ^ 2) := by
  classical
  have hL : 0 ≤ L := (hm 0).trans (hmL 0)
  rcases hL.eq_or_lt with h | hL
  · subst L
    have hz (i) : m i = 0 := (hmL i).antisymm (hm i)
    simp [hz]
  rw [Finset.sum_filter]
  have hterm (i : Fin 3) :
      (if 0 < m i then studentTail 2 (√(2 * ((L / m i) ^ 2 - 1))) else 0)
        = (1 - √(L ^ 2 - (m i) ^ 2) / L) / 2 := by
    by_cases hi : 0 < m i
    · simpa only [hi, ite_true] using studentTail_two_load hi (hmL i)
    · have hz := (not_lt.mp hi).antisymm (hm i)
      simp [hz, Real.sqrt_sq hL.le, hL.ne']
  simp_rw [hterm]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.sum_div]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_ofNat, mul_one]
  constructor <;> intro h
  · apply (one_le_div hL).mp
    linarith
  · have hh : 1 ≤ (∑ i, √(L ^ 2 - (m i) ^ 2)) / L := (one_le_div hL).mpr h
    linarith

/-- The full two - dimensional Student test, including the flattenings, is the
rectangular radical test. -/
theorem studentTail_two_iff_radicalTest {m : Fin 3 → ℝ} (hm : ∀ i, 0 ≤ m i) (L : ℝ) :
    ((∀ i, m i ≤ L) ∧ StudentBound 2 m L) ↔ RadicalTest m L := by
  norm_num only [StudentBound, Nat.cast_ofNat, show (2 : ℝ) - 1 = 1 by norm_num,
    div_one, Real.rpow_two, RadicalTest]
  exact and_congr_right (fun hmL ↦ studentTail_two_sum_iff m hm hmL)

end LinearAlgebra.SpectralBooks

end OAI

import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Gaussian smoothing of the absolute projections in the triangle-density argument -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology ContDiff

section

/-- The one-variable profile used to recover the even moments of a hemisphere restriction. -/
noncomputable def gaussianAbsProfile (a : ℝ) : ℝ :=
  ∫ x, |x + a| ∂gaussianReal 0 1

private theorem gaussianAbsProfile_hasDerivAt (a : ℝ) :
    HasDerivAt gaussianAbsProfile (1 - 2 * (gaussianReal 0 1).real (Iic (-a))) a := by
  let μ := gaussianReal 0 1
  let s := Iic (-a)
  let q := s.indicator (fun _ => (2 : ℝ))
  have hms : MeasurableSet s := measurableSet_Iic
  have hq : Integrable q μ := (integrable_const (2 : ℝ)).indicator hms
  have hqint : ∫ x, (1 - q x) ∂μ = 1 - 2 * μ.real s := by
    rw [integral_sub (integrable_const _) hq, integral_indicator hms]
    simp [mul_comm]
  rw [← hqint]
  apply (hasDerivAt_integral_of_dominated_loc_of_lip (μ := μ) (F := fun t x : ℝ => |x + t|)
    (F' := fun x => 1 - q x) (bound := fun _ => (1 : ℝ)) (s := univ)
    univ_mem ?_ ?_ ?_ ?_ (integrable_const 1) ?_).2
  · exact Eventually.of_forall fun t => by fun_prop
  · exact (IsGaussian.integrable_id.add (integrable_const a)).abs
  · exact (integrable_const (1 : ℝ) |>.sub hq).aestronglyMeasurable
  · refine ae_of_all _ fun x => LipschitzOnWith.of_dist_le_mul ?_
    intro t ht u hu
    simpa [Real.dist_eq] using abs_abs_sub_abs_le_abs_sub (x + t) (x + u)
  · let : NullSingletonClass μ := nullSingletonClass_gaussianReal one_ne_zero
    filter_upwards [μ.ae_ne (-a)] with x hx
    have H := (hasDerivAt_id a).const_add x
    rcases lt_or_gt_of_ne hx with hl | hl
    · have hmem : x ∈ s := hl.le
      norm_num [q, hmem]
      simpa [Function.comp_def] using
        (hasDerivAt_abs_neg (show x + a < 0 by linarith)).comp a H
    · have hmem : x ∉ s := not_le_of_gt hl
      norm_num [q, hmem]
      simpa [Function.comp_def] using
        (hasDerivAt_abs_pos (show 0 < x + a by linarith)).comp a H

private theorem stdGaussian_cdf_hasDerivAt (a : ℝ) :
    HasDerivAt (fun t => (gaussianReal 0 1).real (Iic t)) (gaussianPDFReal 0 1 a) a := by
  let p := gaussianPDFReal 0 1
  have hp : Continuous p := by unfold p gaussianPDFReal; fun_prop
  have hpint : Integrable p := integrable_gaussianPDFReal 0 1
  have heq : (fun t => (gaussianReal 0 1).real (Iic t)) =
      fun t => (∫ x in Iic 0, p x) + ∫ x in (0 : ℝ)..t, p x := by
    funext t
    rw [measureReal_def, gaussianReal_apply_eq_integral _ one_ne_zero,
      ENNReal.toReal_ofReal (integral_nonneg fun x => gaussianPDFReal_nonneg _ _ x),
      ← intervalIntegral.integral_Iic_sub_Iic hpint.integrableOn hpint.integrableOn]
    ring
  rw [heq]
  exact (intervalIntegral.integral_hasDerivAt_right (hp.intervalIntegrable _ _)
    hp.aestronglyMeasurable.stronglyMeasurableAtFilter hp.continuousAt).const_add _

/-- Differentiating the smoothed absolute value twice gives twice the standard Gaussian density. -/
theorem gaussianAbsProfile_hasDerivAt_deriv (a : ℝ) :
    HasDerivAt (deriv gaussianAbsProfile) (2 * gaussianPDFReal 0 1 a) a := by
  have hdf := funext fun t => (gaussianAbsProfile_hasDerivAt t).deriv
  rw [hdf]
  have h := (hasDerivAt_const a (1 : ℝ)).sub
    (((stdGaussian_cdf_hasDerivAt (-a)).comp a (hasDerivAt_id a).neg).const_mul 2)
  simpa [Function.comp_def, gaussianPDFReal] using! h

theorem gaussianAbsProfile_smooth : ContDiff ℝ ∞ gaussianAbsProfile := by
  refine contDiff_infty_iff_deriv.mpr ⟨fun a => (gaussianAbsProfile_hasDerivAt a).differentiableAt, ?_⟩
  refine contDiff_infty_iff_deriv.mpr
    ⟨fun a => (gaussianAbsProfile_hasDerivAt_deriv a).differentiableAt, ?_⟩
  rw [funext fun a => (gaussianAbsProfile_hasDerivAt_deriv a).deriv]
  unfold gaussianPDFReal
  fun_prop

/-- All even derivatives at the origin detect a moment, including the constant moment. -/
theorem gaussianAbsProfile_even_deriv_ne_zero (j : ℕ) :
    iteratedDeriv (2 * j) gaussianAbsProfile 0 ≠ 0 := by
  cases j with
  | zero =>
    simp only [Nat.mul_zero, iteratedDeriv_zero, gaussianAbsProfile, add_zero]
    let : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
    apply ne_of_gt
    rw [integral_pos_iff_support_of_nonneg (fun x => abs_nonneg x) IsGaussian.integrable_id.abs]
    have hs : Function.support (fun x : ℝ => |x|) = ({0} : Set ℝ)ᶜ := by ext x; simp
    simp [hs, measure_compl]
  | succ k =>
    rw [show 2 * (k+1) = 2 * k + 1 + 1 by omega,
      iteratedDeriv_succ', iteratedDeriv_succ',
      funext fun a => (gaussianAbsProfile_hasDerivAt_deriv a).deriv]
    have hp : (fun a => 2 * gaussianPDFReal 0 1 a) =
        fun a : ℝ => (2 / Real.sqrt (2 * Real.pi)) * Real.exp (-(a^2 / 2)) := by
      funext a
      simp [gaussianPDFReal, div_eq_mul_inv, mul_assoc]
    rw [hp, iteratedDeriv_const_mul_field, iteratedDeriv_eq_iterate,
      Polynomial.deriv_gaussian_eq_hermite_mul_gaussian,
      ← Polynomial.coeff_zero_eq_aeval_zero']
    have hc := Polynomial.coeff_hermite_explicit k 0
    simp at hc
    rw [hc]
    simp [Nat.doubleFactorial_pos _ |>.ne', (Real.sqrt_pos.mpr Real.pi_pos).ne']

/-- Differentiation on compact parameter sets with an integrable signed weight.
The bound on the derivative comes from the continuous kernel on a compact rectangle. -/
private theorem integral_weightedKernel_hasDerivAt {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {μ : Measure X} {w : X → ℝ} (hw : Integrable w μ) (K K' : ℝ × X → ℝ)
    (hK : Continuous K) (hK' : Continuous K')
    (hd : ∀ t x, HasDerivAt (fun s => K (s,x)) (K' (t,x)) t) (a : ℝ) :
    HasDerivAt (fun t => ∫ x, w x * K (t,x) ∂μ) (∫ x, w x * K' (a,x) ∂μ) a := by
  let s := Icc (a - 1) (a + 1)
  have hs : s ∈ 𝓝 a := Icc_mem_nhds (by linarith) (by linarith)
  obtain ⟨M, hM⟩ := ((isCompact_Icc (a := a - 1) (b := a + 1)).prod (isCompact_univ (X := X))).bddAbove_image
    (f := fun p : ℝ × X => |K' p|) hK'.abs.continuousOn
  obtain ⟨N, hN⟩ := (isCompact_univ (X := X)).bddAbove_image
    (f := fun x : X => |K (a,x)|) (hK.comp (continuous_const.prodMk continuous_id)).abs.continuousOn
  have hm (t : ℝ) : AEStronglyMeasurable (fun x => w x * K (t,x)) μ :=
    hw.aestronglyMeasurable.mul (hK.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun t x => w x * K (t,x)) (F' := fun t x => w x * K' (t,x))
    (bound := fun x => |w x| * M) hs (.of_forall hm) ?_ ?_ ?_ (hw.abs.mul_const M) ?_).2
  · apply (hw.abs.mul_const N).mono' (hm a)
    refine ae_of_all _ fun x => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hN ⟨x, mem_univ _, rfl⟩) (abs_nonneg _)
  · exact hw.aestronglyMeasurable.mul
      (hK'.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · refine ae_of_all _ fun x t ht => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hM ⟨(t,x), ⟨ht, mem_univ _⟩, rfl⟩) (abs_nonneg _)
  · exact ae_of_all _ fun x t _ => (hd t x).const_mul (w x)

/-- The Gaussian averages used in the proof of triangle density determine every even
moment of a bounded continuous projection. An integrable real weight allows signed measures. -/
theorem even_moments_zero_of_gaussianAbsProfile {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {μ : Measure X} {w : X → ℝ} (hw : Integrable w μ) {u : X → ℝ} (hu : Continuous u)
    (hann : ∀ t : ℝ, ∫ x, w x * gaussianAbsProfile (t * u x) ∂μ = 0) (j : ℕ) :
    ∫ x, w x * u x ^ (2 * j) ∂μ = 0 := by
  let K (n : ℕ) (p : ℝ × X) :=
    u p.2 ^ n * iteratedDeriv n gaussianAbsProfile (p.1 * u p.2)
  have hc (n : ℕ) : Continuous (K n) :=
    ((hu.comp continuous_snd).pow n).mul
      ((gaussianAbsProfile_smooth.continuous_iteratedDeriv n (by simp)).comp
        (continuous_fst.mul (hu.comp continuous_snd)))
  have hz (n : ℕ) : ∀ t : ℝ, ∫ x, w x * K n (t,x) ∂μ = 0 := by
    induction n with
    | zero => simpa [K] using hann
    | succ n ih =>
      intro t
      have hd (a : ℝ) (x : X) : HasDerivAt (fun s => K n (s,x)) (K (n+1) (a,x)) a := by
        have hl := (gaussianAbsProfile_smooth.differentiable_iteratedDeriv n (by exact_mod_cast ENat.natCast_lt_top n)
          (a * u x)).hasDerivAt
        convert! ((hl.comp a ((hasDerivAt_id a).mul_const (u x))).const_mul (u x ^ n)) using 1
        simp [K, iteratedDeriv_succ, pow_succ]
        ring
      have H := integral_weightedKernel_hasDerivAt hw (K n) (K (n+1)) (hc n) (hc (n+1)) hd t
      rw [funext ih] at H
      simpa using H.deriv.symm
  have H := hz (2 * j) 0
  simp only [K, zero_mul, ← mul_assoc, integral_mul_const, mul_eq_zero] at H
  exact H.resolve_right (gaussianAbsProfile_even_deriv_ne_zero j)

open scoped RealInnerProductSpace

/-- A finite signed weight on unit vectors annihilating all absolute projections
also annihilates every even power of every linear projection. -/
theorem even_moments_zero_of_abs_projections {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {w : X → ℝ} (hw : Integrable w μ) {u : X → E} (hu : Continuous u)
    (hunit : ∀ x, ‖u x‖ = 1) (hann : ∀ g : E, ∫ x, w x * |⟪u x, g⟫| ∂μ = 0)
    (z : E) (j : ℕ) : ∫ x, w x * ⟪u x, z⟫ ^ (2 * j) ∂μ = 0 := by
  apply even_moments_zero_of_gaussianAbsProfile hw (hu.inner continuous_const) _ j
  intro t
  let γ := stdGaussian E
  let F (x : X) (g : E) := w x * |⟪u x, g + t • z⟫|
  have hdist (x : X) : γ.map (innerSL ℝ (u x)) = gaussianReal 0 1 := by
    rw [IsGaussian.map_eq_gaussianReal]
    simp only [γ, integral_strongDual_stdGaussian, variance_dual_stdGaussian,
      innerSL_apply_norm, hunit, one_pow, Real.toNNReal_one]
  have hinner (x : X) : w x * gaussianAbsProfile (t * ⟪u x, z⟫) = ∫ g, F x g ∂γ := by
    unfold F gaussianAbsProfile
    rw [← hdist x, integral_map (by fun_prop) (by fun_prop), integral_const_mul]
    simp [inner_add_right, real_inner_smul_right, innerSL_apply_apply ℝ]
  simp_rw [hinner]
  have hFi : Integrable (Function.uncurry F) (μ.prod γ) := by
    refine (hw.abs.mul_prod ((IsGaussian.integrable_id (μ := γ)).norm.add
      (integrable_const ‖t • z‖))).mono' ?_ ?_
    · apply hw.aestronglyMeasurable.comp_fst.mul
      exact ((hu.comp continuous_fst).inner
        (continuous_snd.add continuous_const) (𝕜 := ℝ)).abs.aestronglyMeasurable
    · refine ae_of_all _ fun p => ?_
      change ‖w p.1 * |⟪u p.1, p.2 + t • z⟫|‖ ≤ |w p.1| * (‖p.2‖ + ‖t • z‖)
      rw [Real.norm_eq_abs, abs_mul, abs_abs]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      calc
        _ ≤ ‖u p.1‖ * ‖p.2 + t • z‖ := abs_real_inner_le_norm _ _
        _ = ‖p.2 + t • z‖ := by rw [hunit, one_mul]
        _ ≤ _ := norm_add_le _ _
  rw [integral_integral_swap hFi]
  simp only [F, hann, integral_zero]

end

end SpectralBooks
end LinearAlgebra
end OAI

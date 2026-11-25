import OAI.LinearAlgebra.SpectralBooks.TriangleWidth
import OAI.LinearAlgebra.SpectralBooks.WidthSphere
import OAI.Probability.Perceptron.Sphere.GaussianPolar

/-! # Gaussian and spherical forms of mean width -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal RealInnerProductSpace
section

section Coordinates
open SphericalPerceptronFreeEnergy

private theorem exists_gaussian_radial_factor (d : ℕ) :
    ∃ k : ℝ, ∀ (f : Spin (d+1) → ℝ) (_ : Measurable f)
      (_ : ∀ (r : ℝ), 0 < r → ∀ x, f (r • x) = r * f x),
      (∫ x, f x ∂stdGaussian (Spin (d+1))) =
        k * ∫ n : sphere (0 : Spin (d+1)) 1, f n.1 ∂(volume : Measure (Spin (d+1))).toSphere := by
  let R := Set.Ioi (0 : ℝ)
  let S := sphere (0 : Spin (d+1)) 1
  let μ := gaussianRadiusLaw d
  let ν := (volume : Measure (Spin (d+1))).toSphere
  let ρ : Measure (R × S) := μ.prod (unitSphereLaw (d+1))
  let scale : R × S → Spin (d+1) := fun p ↦ p.1.1 • p.2.1
  have hm : Measurable scale := measurable_fst.subtype_val.smul measurable_snd.subtype_val
  have he : ρ.map scale = stdGaussian (Spin (d+1)) := by
    apply Measure.ext_of_lintegral
    intro g hg
    rw [lintegral_map hg hm, stdGaussian_polar_lintegral d g hg]
    exact lintegral_prod _ (hg.comp hm).aemeasurable
  refine ⟨(∫ r : R, r.1 ∂μ) * (ν Set.univ)⁻¹.toReal, ?_⟩
  intro f hf hscale
  rw [← he, integral_map hm.aemeasurable hf.aestronglyMeasurable]
  change (∫ p : R × S, f (p.1.1 • p.2.1) ∂μ.prod _) = _
  have hsplit (p : R × S) : f (p.1.1 • p.2.1) = p.1.1 * f p.2.1 := hscale _ p.1.2 _
  simp only [hsplit]
  rw [integral_prod_mul (fun r : R ↦ r.1) (fun n : S ↦ f n.1), unitSphereLaw, integral_smul_measure, smul_eq_mul, mul_assoc]

end Coordinates

open AffineBernstein
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
local notation "S" => sphere (0 : E) 1
local notation "σ₀" => Measure.toSphere (volume : Measure E)

private theorem exists_gaussian_factor (e : S) :
    ∃ k : ℝ, ∀ (f : E → ℝ) (_ : Measurable f)
      (_ : ∀ (r : ℝ), 0 < r → ∀ x, f (r • x) = r * f x),
      (∫ x, f x ∂stdGaussian E) = k * ∫ n : S, f n.1 ∂σ₀ := by
  have hne : (e : E) ≠ 0 := by
    intro h
    have he : ‖(e : E)‖ = 1 := by simp
    simp [h] at he
  let _ : Nontrivial E := ⟨_, _, hne⟩
  obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero (Module.finrank_pos (R := ℝ) (M := E)).ne'
  let g : EuclideanSpace ℝ (Fin (d+1)) ≃ₗᵢ[ℝ] E := by
    change EuclideanSpace ℝ (Fin d.succ) ≃ₗᵢ[ℝ] E
    rw [← hd]
    exact (stdOrthonormalBasis ℝ E).repr.symm
  obtain ⟨k, hk⟩ := exists_gaussian_radial_factor d
  refine ⟨k, fun f hf hscale ↦ ?_⟩
  have hgm : MeasurePreserving g (stdGaussian _) (stdGaussian E) :=
    ⟨g.continuous.measurable, stdGaussian_map g⟩
  have h₁ := hgm.integral_comp g.toHomeomorph.measurableEmbedding f
  have h₂ := (linearIsometrySphere_measurePreserving g).integral_comp
    (linearIsometrySphereHomeomorph g).measurableEmbedding (fun n : S ↦ f n.1)
  rw [← h₁, ← h₂]
  exact hk (f ∘ g) (hf.comp g.continuous.measurable) (fun r hr x ↦ by
    simp only [Function.comp_apply, map_smul, hscale r hr])

/-- The normalized spherical integral agrees with the Gaussian width integral for
any measurable, positively homogeneous integrand of degree one. -/
theorem gaussian_integral_eq_widthSphereMeasure (e : S) (f : E → ℝ) (hf : Measurable f)
    (hscale : ∀ (r : ℝ), 0 < r → ∀ x, f (r • x) = r * f x) :
    Real.sqrt (2 * Real.pi) * (∫ x, f x ∂stdGaussian E) =
      ∫ n : S, f n.1 ∂widthSphereMeasure e := by
  classical
  obtain ⟨k, hk⟩ := exists_gaussian_factor e
  let seg (x : E) := max 0 ⟪x, (e : E)⟫
  have hseg : Real.sqrt (2 * Real.pi) * (∫ x, seg x ∂stdGaussian E) = 1 := by
    simpa only [meanWidth, support, Finset.sup'_insert (Finset.singleton_nonempty _),
      Finset.sup'_singleton, inner_zero_right, dist_zero_left, seg,
      mem_sphere_zero_iff_norm.mp e.prop] using meanWidth_pair (0 : E) (e : E)
  have hmoment := hk seg (measurable_const.max (by fun_prop)) (fun r hr x ↦ by
    simp [seg, real_inner_smul_left, mul_max_of_nonneg _ _ hr.le])
  change (∫ x, seg x ∂stdGaussian E) = k * segmentMoment e at hmoment
  rw [hmoment, ← mul_assoc] at hseg
  have hcal : Real.sqrt (2 * Real.pi) * k = (segmentMoment e)⁻¹ := by
    rw [← one_div, eq_div_iff (segmentMoment_pos e).ne']
    exact hseg
  rw [hk f hf hscale, ← mul_assoc, hcal, widthSphereMeasure, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (segmentMoment_pos e).le), smul_eq_mul]

/-- The two definitions of mean width in the flat diagonal law. -/
theorem meanWidth_eq_sphereIntegral (e : S) (T : Finset E) (hT : T.Nonempty) :
    meanWidth T hT = ∫ n : S, support T hT n.1 ∂widthSphereMeasure e := by
  apply gaussian_integral_eq_widthSphereMeasure
  · have heq : support T hT = T.sup' hT (fun x u ↦ ⟪u, x⟫) := by
      funext u
      exact (Finset.sup'_apply hT (fun (x u : E) ↦ ⟪u, x⟫) u).symm
    rw [heq]
    exact Finset.sup'_induction hT _ (p := fun f : E → ℝ ↦ Measurable f)
      (fun _ hg _ hh ↦ hg.max hh) (fun x _ ↦ by fun_prop)
  · intro r hr x
    unfold support
    simp only [real_inner_smul_left]
    exact (Finset.apply_sup'_eq_sup'_comp hT (r * ·)
      (fun b c ↦ mul_max_of_nonneg b c hr.le) (f := fun v ↦ ⟪x, v⟫)).symm

/-- The normal-cone increment on the unit sphere in the width-marginal formula. -/
theorem gaussian_normalConeIntegral_eq_sphereIntegral (e : S) (T : Finset E) (v : E) :
    Real.sqrt (2 * Real.pi) * (∫ w in normalConeAtZero T, max ⟪w, v⟫ 0 ∂stdGaussian E) =
      ∫ n : S in Subtype.val ⁻¹' normalConeAtZero T,
        max ⟪(n : E), v⟫ 0 ∂widthSphereMeasure e := by
  classical
  let C := normalConeAtZero T
  have hm : MeasurableSet C := measurableSet_normalConeAtZero T
  have hs (r : ℝ) (hr : 0 < r) (x : E) : r • x ∈ C ↔ x ∈ C := by
    change (∀ v ∈ T, ⟪r • x, v⟫ ≤ 0) ↔ (∀ v ∈ T, ⟪x, v⟫ ≤ 0)
    simp only [real_inner_smul_left, mul_nonpos_iff, hr.le, not_le_of_gt hr,
      true_and, false_and, or_false]
  have h := gaussian_integral_eq_widthSphereMeasure e
    (C.indicator fun w ↦ max ⟪w, v⟫ 0) ((by fun_prop : Measurable (fun w ↦ max ⟪w, v⟫ 0)).indicator hm)
    (fun r hr x ↦ by
      by_cases hx : x ∈ C
      · simp [Set.indicator_of_mem hx, Set.indicator_of_mem ((hs r hr x).2 hx),
          real_inner_smul_left, mul_max_of_nonneg _ _ hr.le]
      · simp [Set.indicator_of_notMem hx, Set.indicator_of_notMem (mt (hs r hr x).1 hx)])
  rw [← integral_indicator hm, ← integral_indicator (hm.preimage measurable_subtype_coe)]
  exact h

/-- Translation adds a linear function to the support. Its Gaussian expectation vanishes. -/
theorem meanWidth_translate [DecidableEq E] (T : Finset E) (hT : T.Nonempty) (a : E) :
    meanWidth (T.image (· + a)) (hT.image _) = meanWidth T hT := by
  have heq (u : E) : support (T.image (· + a)) (hT.image _) u =
      support T hT u + ⟪u, a⟫ := by
    simp only [support, Finset.sup'_image, Function.comp_apply, inner_add_right,
      Finset.sup'_add]
  have hlin : (∫ u, ⟪u, a⟫ ∂stdGaussian E) = 0 := by
    simpa only [innerSL_apply_apply, real_inner_comm a] using
      integral_strongDual_stdGaussian (innerSL ℝ a)
  simp only [meanWidth, heq, integral_add (integrable_support T hT)
    ((IsGaussian.integrable_fun_id (μ := stdGaussian E)).inner_const a), hlin, add_zero]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

/-- Embedding the sites linearly and isometrically preserves their mean width,
including when the ambient dimension increases. -/
theorem meanWidth_linearIsometry [DecidableEq F] (i : E →ₗᵢ[ℝ] F)
    (T : Finset E) (hT : T.Nonempty) :
    meanWidth (T.image i) (hT.image _) = meanWidth T hT := by
  let p := ContinuousLinearMap.adjoint i.toContinuousLinearMap
  have hmap : (stdGaussian F).map p = stdGaussian E := by
    apply Measure.ext_of_charFun
    funext t
    rw [charFun_apply, integral_map p.continuous.aemeasurable (by fun_prop)]
    simp only [p, ContinuousLinearMap.adjoint_inner_left]
    change charFun (stdGaussian F) (i t) = charFun (stdGaussian E) t
    simp [charFun_stdGaussian]
  have heq (u : F) : support (T.image i) (hT.image _) u = support T hT (p u) := by
    simp only [support, Finset.sup'_image, Function.comp_apply, p,
      ContinuousLinearMap.adjoint_inner_left, LinearIsometry.coe_toContinuousLinearMap]
  have h := integral_map p.continuous.aemeasurable
    (f := support T hT) (μ := stdGaussian F) (by
      rw [hmap]
      exact (integrable_support T hT).aestronglyMeasurable)
  rw [hmap] at h
  simp only [meanWidth, heq, h]

/-- The support-integral mean width is invariant under affine isometric embeddings. -/
theorem meanWidth_affineIsometry [DecidableEq F] (i : E →ᵃⁱ[ℝ] F)
    (T : Finset E) (hT : T.Nonempty) :
    meanWidth (T.image i) (hT.image _) = meanWidth T hT := by
  have heq : T.image i = (T.image i.linearIsometry).image (· + i 0) := by
    rw [Finset.image_image]
    apply Finset.image_congr
    intro x _
    simpa using i.map_vadd (0 : E) x
  rw [show meanWidth (T.image i) (hT.image _) =
      meanWidth ((T.image i.linearIsometry).image (· + i 0)) ((hT.image _).image _) by simp only [← heq],
    meanWidth_translate _ (hT.image _) _, meanWidth_linearIsometry i.linearIsometry T hT]

end

end

end SpectralBooks
end LinearAlgebra
end OAI

import OAI.LinearAlgebra.SpectralBooks.Width
import OAI.LinearAlgebra.SpectralBooks.GaussianAbsolute

/-! # Gaussian mean width of segments and triangles -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem normalized_integral_abs_inner (x : E) :
    Real.sqrt (2 * Real.pi) * ∫ u, |⟪u, x⟫| ∂(stdGaussian E) = 2 * ‖x‖ := by
  let L := innerSL ℝ x
  have hmap : (stdGaussian E).map L = (gaussianReal 0 1).map (‖x‖ * ·) := by
    rw [IsGaussian.map_eq_gaussianReal, gaussianReal_map_const_mul,
      integral_strongDual_stdGaussian, variance_dual_stdGaussian]
    simp [L, Real.toNNReal_of_nonneg (sq_nonneg ‖x‖)]
  have hi : (∫ u, |⟪u, x⟫| ∂(stdGaussian E)) =
      ‖x‖ * ∫ t : ℝ, |t| ∂(gaussianReal 0 1) := by
    calc
      _ = ∫ t : ℝ, |t| ∂((stdGaussian E).map L) := by
        rw [integral_map L.continuous.aemeasurable (by fun_prop)]
        simp only [L, innerSL_apply_apply, real_inner_comm x]
      _ = ∫ t : ℝ, |‖x‖ * t| ∂(gaussianReal 0 1) := by
        rw [hmap, integral_map (by fun_prop) (by fun_prop)]
      _ = _ := by simp [abs_mul, integral_const_mul]
  rw [hi, mul_left_comm, normalized_integral_abs_gaussianReal, mul_comm]

private theorem twice_range_of_three (a b c : ℝ) :
    2 * (max a (max b c) + max (-a) (max (-b) (-c))) =
      |a - b| + |b - c| + |c - a| := by
  grind [abs_eq_max_neg]

private theorem integral_precomp_neg (f : E → ℝ) (hf : AEStronglyMeasurable f (stdGaussian E)) :
    (∫ u, f (-u) ∂(stdGaussian E)) = ∫ u, f u ∂(stdGaussian E) := by
  let e : E ≃ₗᵢ[ℝ] E := LinearIsometryEquiv.neg ℝ
  have he := stdGaussian_map e
  calc
    _ = ∫ u, f u ∂((stdGaussian E).map e) :=
      (integral_map e.continuous.aemeasurable (by simpa only [he] using hf)).symm
    _ = _ := by rw [he]

/-- The Gaussian mean width of three vertices equals their half-perimeter, allowing
repeated or collinear vertices. -/
theorem meanWidth_triangle [DecidableEq E] (a b c : E) :
    meanWidth {a, b, c} (Finset.insert_nonempty _ _) =
      (dist a b + dist b c + dist c a) / 2 := by
  let f (u : E) := max ⟪u, a⟫ (max ⟪u, b⟫ ⟪u, c⟫)
  have hproj (v : E) : Integrable (fun u : E ↦ ⟪u, v⟫) (stdGaussian E) :=
    (IsGaussian.integrable_fun_id (μ := stdGaussian E)).inner_const v
  have hf : Integrable f (stdGaussian E) := (hproj a).sup ((hproj b).sup (hproj c))
  have hf' : Integrable (fun u ↦ f (-u)) (stdGaussian E) := by
    simp only [f, inner_neg_left]
    exact (hproj a).neg.sup ((hproj b).neg.sup (hproj c).neg)
  have hwidth (u : E) :
      2 * (f u + f (-u)) = |⟪u, a - b⟫| + |⟪u, b - c⟫| + |⟪u, c - a⟫| := by
    simpa only [f, inner_neg_left, inner_sub_right] using
      twice_range_of_three ⟪u, a⟫ ⟪u, b⟫ ⟪u, c⟫
  have heq := congrArg (fun g : E → ℝ ↦ ∫ u, g u ∂(stdGaussian E)) (funext hwidth)
  rw [integral_const_mul, integral_add hf hf', integral_precomp_neg f hf.aestronglyMeasurable,
    integral_add ((hproj (a - b)).abs.fun_add (hproj (b - c)).abs) (hproj (c - a)).abs,
    integral_add (hproj (a - b)).abs (hproj (b - c)).abs] at heq
  have hs : support {a, b, c} (Finset.insert_nonempty _ _) = f := by
    funext u
    simp only [support, Finset.sup'_insert (Finset.insert_nonempty _ _),
      Finset.sup'_insert (Finset.singleton_nonempty _), Finset.sup'_singleton, f]
  unfold meanWidth
  rw [hs]
  simp only [dist_eq_norm]
  linarith only [congrArg (Real.sqrt (2 * Real.pi) * ·) heq,
    normalized_integral_abs_inner (a - b), normalized_integral_abs_inner (b - c),
    normalized_integral_abs_inner (c - a)]

/-- A segment has normalized mean width equal to its length. -/
theorem meanWidth_pair [DecidableEq E] (a b : E) :
    meanWidth {a, b} (Finset.insert_nonempty _ _) = dist a b := by
  simpa [dist_comm b a] using meanWidth_triangle a b b

end

end SpectralBooks
end LinearAlgebra
end OAI

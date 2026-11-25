import OAI.Analysis.AffineBernstein.SphereIsometry

/-! # Surface measure in the flat diagonal law

The area measure on the unit sphere is scaled by the reciprocal of the mean
support of a unit segment, so that every segment has width equal to its length.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open MeasureTheory Metric AffineBernstein
open scoped ENNReal InnerProductSpace

section
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
local notation "S" => sphere (0 : E) 1
local notation "σ₀" => Measure.toSphere (volume : Measure E)

/-- The support integral of a unit segment against surface area. -/
def segmentMoment (e : S) := ∫ n : S, max 0 ⟪(n : E), (e : E)⟫_ℝ ∂σ₀

theorem segmentMoment_pos (e : S) : 0 < segmentMoment e := by
  have he : ‖(e : E)‖ = 1 := by simp
  apply Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := e)
  · exact continuous_const.max (continuous_subtype_val.inner continuous_const)
  · exact HasCompactSupport.of_compactSpace _
  · exact fun _ ↦ le_max_left _ _
  · simp [he]

theorem segmentMoment_eq (u v : S) : segmentMoment u = segmentMoment v := by
  let g := Submodule.reflection (ℝ ∙ ((u : E) - v))ᗮ
  have huv : g u = v := Submodule.reflection_sub (by simp)
  have h := (linearIsometrySphere_measurePreserving g).integral_comp
    (linearIsometrySphereHomeomorph g).measurableEmbedding (fun n : S ↦ max 0 ⟪(n : E), (v : E)⟫_ℝ)
  unfold segmentMoment
  convert h using 1
  apply integral_congr_ae
  filter_upwards with n
  simp [← huv, g.inner_map_map]

/-- The rotation-invariant surface measure in the sphere formula for mean width. -/
def widthSphereMeasure (e : S) : Measure S := ENNReal.ofReal (segmentMoment e)⁻¹ • σ₀

theorem widthSphereMeasure_eq (e v : S) : widthSphereMeasure e = widthSphereMeasure v := by
  simp only [widthSphereMeasure, segmentMoment_eq e v]

instance (e : S) : IsFiniteMeasure (widthSphereMeasure e) :=
  Measure.smul_finite σ₀ ENNReal.ofReal_ne_top

instance (e : S) : Measure.IsOpenPosMeasure (widthSphereMeasure e) :=
  Measure.isOpenPosMeasure_smul σ₀ (ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr (segmentMoment_pos e)))

theorem widthSphereMeasure_rotation (e : S) (g : E ≃ₗᵢ[ℝ] E) :
    MeasurePreserving (linearIsometrySphereHomeomorph g) (widthSphereMeasure e) (widthSphereMeasure e) :=
  (linearIsometrySphere_measurePreserving g).smul_measure _

theorem widthSphereMeasure_segment (e v : S) :
    ∫ n : S, max 0 ⟪(n : E), (v : E)⟫_ℝ ∂widthSphereMeasure e = 1 := by
  rw [widthSphereMeasure, integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.mpr (segmentMoment_pos e).le)]
  change (segmentMoment e)⁻¹ * segmentMoment v = 1
  rw [segmentMoment_eq v e, inv_mul_cancel₀ (segmentMoment_pos e).ne']

theorem widthSphereMeasure_segment_from_zero (e : S) (v : E) :
    ∫ n : S, max 0 ⟪(n : E), v⟫_ℝ ∂widthSphereMeasure e = ‖v‖ := by
  by_cases hv : v = 0
  · simp [hv]
  let w : S := ⟨NormedSpace.normalize v, by simp [NormedSpace.norm_normalize hv]⟩
  have hw : ‖v‖ • (w : E) = v := NormedSpace.norm_smul_normalize v
  calc
    _ = ∫ n : S, ‖v‖ * max 0 ⟪(n : E), (w : E)⟫_ℝ ∂widthSphereMeasure e := by
      apply integral_congr_ae
      filter_upwards with n
      conv_lhs => rw [← hw, real_inner_smul_right]
      rw [mul_max_of_nonneg _ _ (norm_nonneg v), mul_zero]
    _ = _ := by rw [integral_const_mul, widthSphereMeasure_segment, mul_one]

theorem widthSphereMeasure_inner (e : S) (v : E) :
    ∫ n : S, ⟪(n : E), v⟫_ℝ ∂widthSphereMeasure e = 0 := by
  let g : E ≃ₗᵢ[ℝ] E := LinearIsometryEquiv.neg ℝ
  have h := (widthSphereMeasure_rotation e g).integral_comp
    (linearIsometrySphereHomeomorph g).measurableEmbedding (fun n : S ↦ ⟪(n : E), v⟫_ℝ)
  simp [g, integral_neg] at h
  linarith

theorem widthSphereMeasure_segment_length (e : S) (x y : E) :
    ∫ n : S, max ⟪(n : E), x⟫_ℝ ⟪(n : E), y⟫_ℝ ∂widthSphereMeasure e = dist x y := by
  have hsub : Continuous (fun n : S ↦ max 0 ⟪(n : E), (y - x)⟫_ℝ) :=
    continuous_const.max (continuous_subtype_val.inner continuous_const)
  have hx : Continuous (fun n : S ↦ ⟪(n : E), x⟫_ℝ) := continuous_subtype_val.inner continuous_const
  calc
    _ = ∫ n : S, ⟪(n : E), x⟫_ℝ + max 0 ⟪(n : E), (y - x)⟫_ℝ ∂widthSphereMeasure e := by
      apply integral_congr_ae
      filter_upwards with n
      rw [inner_sub_right, add_max, add_zero, add_sub_cancel]
    _ = _ := by
      rw [integral_add (hx.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
        (hsub.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)),
        widthSphereMeasure_inner, widthSphereMeasure_segment_from_zero, zero_add, dist_eq_norm, norm_sub_rev]

end
end

end SpectralBooks
end LinearAlgebra
end OAI

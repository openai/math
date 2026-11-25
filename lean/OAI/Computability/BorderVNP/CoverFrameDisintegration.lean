import OAI.Computability.BorderVNP.CoverFrameCoordinates
import OAI.Computability.BorderVNP.CoverFramePositionLaw
import OAI.Computability.BorderVNP.ShortenEpochIdeal
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Product Haar law in position and angular coordinates

In the upper-half-plane trivialization, a left translation of the frame group acts by a
hyperbolic isometry on positions and by a position-dependent rotation on each circle.
Thus hyperbolic area times angular Haar pushes forward to a Haar measure on frames.
Restricting to the exact position tile and normalizing gives the independent laws used
for the ideal epoch counts in Section 6.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover.Frame

open MeasureTheory UpperHalfPlane Hecke Set
open scoped ENNReal Pointwise

local instance angular_isHaar : Epoch.angularHaar.IsHaarMeasure := by
  unfold Epoch.angularHaar
  infer_instance

/-- Haar measure in upper-half-plane position and rotation coordinates, with normalized
circle fiber. -/
noncomputable def frameVolume : Measure SL :=
  ((volume : Measure ℍ).prod Epoch.angularHaar).map frameCoordinates.symm

/-- Left matrix multiplication preserves the product expression for frame Haar. -/
instance frameVolume_leftInvariant : frameVolume.IsMulLeftInvariant := by
  constructor
  intro g
  let T (p : ℍ × Circle) := (g • p.1, spinCoordinate (g * p.1.toSL2R) * p.2)
  have hp : MeasurePreserving T ((volume : Measure ℍ).prod Epoch.angularHaar)
      ((volume : Measure ℍ).prod Epoch.angularHaar) := by
    apply (measurePreserving_plane_action g).skew_product (g := fun (z : ℍ) (w : Circle) =>
      spinCoordinate (g * z.toSL2R) * w)
    · apply Continuous.measurable
      exact (continuous_spinCoordinate.comp (continuous_const.mul
        (continuous_toSL2R.comp continuous_fst))).mul continuous_snd
    · exact Filter.Eventually.of_forall fun x =>
        (measurePreserving_mul_left Epoch.angularHaar (spinCoordinate (g*x.toSL2R))).map_eq
  have hcomm : (g * ·) ∘ frameCoordinates.symm = frameCoordinates.symm ∘ T := by
    funext p
    apply frameCoordinates.injective
    exact (translate_frameCoordinates g p).trans (frameCoordinates.apply_symm_apply _).symm
  rw [frameVolume, Measure.map_map (measurable_const_mul _) frameCoordinates.symm.continuous.measurable,
    hcomm, ← Measure.map_map frameCoordinates.symm.continuous.measurable hp.measurable, hp.map_eq]

/-- The explicit product-coordinate measure is Haar on the real frame group. -/
instance frameVolume_isHaar : frameVolume.IsHaarMeasure where
  lt_top_of_isCompact K hK := by
    rw [frameVolume, Measure.map_apply frameCoordinates.symm.continuous.measurable hK.isClosed.measurableSet]
    exact (frameCoordinates.symm.isClosedEmbedding.isCompact_preimage hK).measure_lt_top
  toIsOpenPosMeasure := frameCoordinates.symm.continuous.isOpenPosMeasure_map frameCoordinates.symm.surjective

/-- The full frame tile with every angle at each of the selected positions. -/
def positionFrameTile (l : ℕ) : Set SL := (fun g : SL => g • I) ⁻¹' planeTile l

/-- Restriction and normalization of frame Haar on this tile gives precisely the product
of normalized hyperbolic area with the uniform angular coordinate. -/
theorem frameVolume_disintegration (l : ℕ) :
    (((volume : Measure ℍ) (planeTile l))⁻¹ • frameVolume).restrict (positionFrameTile l) =
      ((positionLaw l).prod Epoch.angularHaar).map frameCoordinates.symm := by
  have htile : frameCoordinates.symm ⁻¹' positionFrameTile l = planeTile l ×ˢ univ := by
    ext p
    change (p.1.toSL2R * spin p.2) • I ∈ planeTile l ↔ p.1 ∈ planeTile l ∧ p.2 ∈ (univ : Set Circle)
    simp [mul_smul, spin_fixes_I]
  have hm : MeasurableSet (positionFrameTile l) := (exact_position_frame_tile l).1
  rw [Measure.restrict_smul, frameVolume, Measure.restrict_map frameCoordinates.symm.continuous.measurable
    hm, htile, ← Measure.prod_restrict, Measure.restrict_univ,
    positionLaw, Measure.prod_smul_left, Measure.map_smul _ frameCoordinates.symm.continuous.measurable.aemeasurable]

/-- The quotient measure is the image of independent position and circle samples, using
the actual tile representatives and the actual quaternion lattice. -/
theorem quotient_frame_disintegration (l : ℕ) :
    tileHaar (frameGroup (l+1)) (((volume : Measure ℍ) (planeTile l))⁻¹ • frameVolume)
      (positionFrameTile l) =
      ((positionLaw l).prod Epoch.angularHaar).map (coset (frameGroup (l+1)) ∘ frameCoordinates.symm) := by
  have hq : Measurable (coset (frameGroup (l+1))) :=
    measurable_quotient_mk' (s := QuotientGroup.rightRel (frameGroup (l+1)))
  rw [tileHaar, frameVolume_disintegration, Measure.map_map hq frameCoordinates.symm.continuous.measurable]

/-- The normalized ambient Haar measure assigns mass one to the exact position frame tile. -/
theorem positionFrameTile_mass (l : ℕ) :
    (((volume : Measure ℍ) (planeTile l))⁻¹ • frameVolume) (positionFrameTile l) = 1 := by
  have h := congrArg (fun μ : Measure SL => μ univ) (frameVolume_disintegration l)
  simpa [Measure.map_apply frameCoordinates.symm.continuous.measurable] using h

end Cover.Frame

end BorderVNP
end Computability
end OAI

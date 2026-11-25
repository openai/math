import OAI.Computability.BorderVNP.CoverLorentzPlaneTile
import OAI.Computability.BorderVNP.CoverFrameNormalizedHaar
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure

/-! # Normalized hyperbolic area on an exact position tile -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover.Frame

open MeasureTheory Matrix Set UpperHalfPlane
open scoped ENNReal NNReal

/-- The real special linear group preserves the hyperbolic area density `dx dy / y²`. -/
theorem measurePreserving_plane_action (g : SL) :
    MeasurePreserving (fun z : ℍ => g • z) volume volume :=
  measurePreserving_smul (g : GL (Fin 2) ℝ) volume

/-- Hyperbolic area is strictly positive on nonempty open subsets of the half plane. -/
instance planeVolume_openPos : (volume : Measure ℍ).IsOpenPosMeasure := by
  constructor
  intro U hU hn hzero
  rw [UpperHalfPlane.volume_def] at hzero
  let w (z : ℍ) : ℝ≥0∞ := ↑((1 / NNReal.mk z.im z.im_pos.le : ℝ≥0) ^ 2)
  have hw : Measurable w := by unfold w; fun_prop
  have hp (z : ℍ) : w z ≠ 0 := by
    have h : (NNReal.mk z.im z.im_pos.le) ≠ 0 := fun e => z.im_ne_zero (congrArg NNReal.toReal e)
    exact ENNReal.coe_ne_zero.mpr (pow_ne_zero _ (div_ne_zero one_ne_zero h))
  have hc := (withDensity_absolutelyContinuous' hw.aemeasurable (Filter.Eventually.of_forall hp)) hzero
  rw [Measure.comap_apply _ UpperHalfPlane.measurableEmbedding_coe.injective
    (fun _ => UpperHalfPlane.measurableEmbedding_coe.measurableSet_image.mpr) _ hU.measurableSet] at hc
  exact (UpperHalfPlane.isOpenEmbedding_coe.isOpenMap _ hU).measure_ne_zero volume (hn.image _) hc

/-- The canonical position tile has finite hyperbolic area. -/
theorem planeTile_volume_ne_top (l : ℕ) : (volume : Measure ℍ) (planeTile l) ≠ ∞ :=
  ((measure_mono (show planeTile l ⊆ dirichlet (l+1) from fun _ h => h.1)).trans_lt
    (dirichlet_compact (l+1)).measure_lt_top).ne

/-- The countably many translates of the position tile cover the upper half plane, hence
its hyperbolic area is positive. -/
theorem planeTile_volume_ne_zero (l : ℕ) : (volume : Measure ℍ) (planeTile l) ≠ 0 := by
  intro hzero
  let A (u : gamma (l+1)) := (fun z : ℍ => gammaSL (l+1) u • z) ⁻¹' planeTile l
  have h : ⋃ u, A u = Set.univ := by
    apply eq_univ_iff_forall.mpr
    intro z
    obtain ⟨u,hu,_⟩ := existsUnique_mem_planeTile l z
    exact mem_iUnion.mpr ⟨u,hu⟩
  apply isOpen_univ.measure_ne_zero (volume : Measure ℍ) univ_nonempty
  rw [← h]
  apply measure_iUnion_null
  intro u
  exact ((measurePreserving_plane_action (gammaSL (l+1) u)).measure_preimage
    (planeTile_measurable l).nullMeasurableSet).trans hzero

/-- The position coordinate of a uniformly sampled frame in the chosen base tile. -/
noncomputable def positionLaw (l : ℕ) : Measure ℍ :=
  ((volume : Measure ℍ) (planeTile l))⁻¹ • volume.restrict (planeTile l)

instance positionLaw_probability (l : ℕ) : IsProbabilityMeasure (positionLaw l) := by
  constructor
  simp only [positionLaw, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ]
  exact ENNReal.inv_mul_cancel (planeTile_volume_ne_zero l) (planeTile_volume_ne_top l)

/-- The reciprocal tile area dominates the normalized position density everywhere. -/
theorem positionLaw_le (l : ℕ) :
    positionLaw l ≤ ((volume : Measure ℍ) (planeTile l))⁻¹ • volume := by
  intro S
  change ((volume : Measure ℍ) (planeTile l))⁻¹ * volume.restrict (planeTile l) S ≤
    ((volume : Measure ℍ) (planeTile l))⁻¹ * volume S
  gcongr
  exact Measure.restrict_le_self

end Cover.Frame

end BorderVNP
end Computability
end OAI

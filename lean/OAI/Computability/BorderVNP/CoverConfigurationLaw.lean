import OAI.Computability.BorderVNP.CoverRelativeChart
import OAI.Computability.BorderVNP.CoverFrameTangentAngle
import OAI.Computability.BorderVNP.ShortenEpochCrossingBins

/-!
# Actual product-frame law for one ordered speed tuple

Each component contributes its base-tile position and physical angle; the
spin parameter is squared on passage to tangent directions. The independent
product of these coordinates splits into independent positions and angles.
The uniform permutation of the component speeds then gives the invariant
configuration law of the canonical bins.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover.Frame

open MeasureTheory Set Filter Hecke Epoch
open scoped Topology ENNReal Classical

variable {I : Type*} [Fintype I]

/-- Normalized law of centers in the product of the tie-resolved position tiles. -/
noncomputable def productPositions (I : Type*) [Fintype I] : Measure (HyperbolicHost I) :=
  (Measure.pi (fun _ : I => positionLaw 0)).map (WithLp.toLp 2)

instance (I : Type*) [Fintype I] : IsProbabilityMeasure (productPositions I) :=
  (Measure.isProbabilityMeasure_map_iff ((WithLp.measurable_toLp 2 _).aemeasurable)).mpr inferInstance

/-- The single factor contributes a base-tile position and the physical unit tangent angle. -/
noncomputable def positionAngle (q : Cosets (lattice 1)) : UpperHalfPlane × Circle :=
  let z := frameCoordinates (quotientRepresentative q)
  (z.1,z.2^2)

/-- The spin-to-angle map retains the product Haar law. -/
theorem positionAngle_preserving :
    MeasurePreserving positionAngle baseHaar ((positionLaw 0).prod angularHaar) :=
  (physicalAngle_preserving 0).comp quotient_coordinates_preserving

/-- Chart for a fixed ordered speed tuple in the full product host. -/
noncomputable def segmentChart (speed : I → ℝ) (p : Equiv.Perm I) (q : I → Cosets (lattice 1)) :
    HyperbolicHost I × PiLp 2 (fun _ : I => ℂ) :=
  (WithLp.toLp 2 (fun i => (positionAngle (q i)).1), fromAngles speed p (fun i => (positionAngle (q i)).2))

omit [Fintype I] in
private theorem fromAngles_continuous (speed : I → ℝ) (p : Equiv.Perm I) :
    Continuous (fromAngles speed p) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  exact (continuous_const_smul (speed (p i))).comp (continuous_subtype_val.comp (continuous_apply i))

/-- Ideal law for a specified permutation before averaging over permutations. -/
noncomputable def classLaw (speed : I → ℝ) (p : Equiv.Perm I) :=
  (productPositions I).prod ((Measure.pi (fun _ : I => angularHaar)).map (fromAngles speed p))

/-- Recovery of the whole configuration from independent quotient Haar frames. -/
theorem segmentChart_preserving (speed : I → ℝ) (p : Equiv.Perm I) :
    MeasurePreserving (segmentChart speed p) (Measure.pi (fun _ : I => baseHaar)) (classLaw speed p) := by
  have each := measurePreserving_pi (fun _ : I => baseHaar)
    (fun _ => (positionLaw 0).prod angularHaar) (fun _ => positionAngle_preserving)
  have split := measurePreserving_arrowProdEquivProdArrow UpperHalfPlane Circle I
    (fun _ => positionLaw 0) (fun _ => angularHaar)
  have base : MeasurePreserving (WithLp.toLp 2 : (I → UpperHalfPlane) → HyperbolicHost I)
      (Measure.pi (fun _ : I => positionLaw 0)) (productPositions I) :=
    ⟨WithLp.measurable_toLp _ _,rfl⟩
  have dir : MeasurePreserving (fromAngles speed p) (Measure.pi (fun _ : I => angularHaar))
      ((Measure.pi (fun _ : I => angularHaar)).map (fromAngles speed p)) :=
    ⟨(fromAngles_continuous speed p).measurable,rfl⟩
  exact (base.prod dir).comp (split.comp each)

/-- The segment chart is continuous away from the finite union of factor seams. -/
theorem segmentChart_ae_continuous (speed : I → ℝ) (p : Equiv.Perm I) :
    ∀ᵐ q ∂Measure.pi (fun _ : I => baseHaar), ContinuousAt (segmentChart speed p) q := by
  have h (i : I) : ∀ᵐ q ∂Measure.pi (fun _ : I => baseHaar), ContinuousAt quotientRepresentative (q i) :=
    (Measure.quasiMeasurePreserving_eval _ i).ae quotientRepresentative_ae_continuous
  filter_upwards [Filter.eventually_all.mpr h] with q hq
  have each (i : I) : ContinuousAt (fun r : I → Cosets (lattice 1) => positionAngle (r i)) q := by
    have hc : ContinuousAt (fun r : I → Cosets (lattice 1) => frameCoordinates (quotientRepresentative (r i))) q :=
      frameCoordinates.continuous.continuousAt.comp
        ((hq i).comp (f := fun r : I → Cosets (lattice 1) => r i) (continuous_apply i).continuousAt)
    exact hc.fst.prodMk (hc.snd.pow 2)
  exact ((PiLp.continuous_toLp 2 _).continuousAt.comp (continuousAt_pi.mpr fun i => (each i).fst)).prodMk
    ((fromAngles_continuous speed p).continuousAt.comp (continuousAt_pi.mpr fun i => (each i).snd))

private theorem mixed_product {X Y J : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [Fintype J] (loc : Measure X) (m : J → Measure Y) [∀ j, SFinite (m j)] (c : ℝ≥0∞) :
    loc.prod (c • ∑ j, m j) = c • ∑ j, loc.prod (m j) := by
  rw [← Measure.sum_fintype m, ← Measure.sum_fintype (fun j => loc.prod (m j))]
  rw [Measure.prod_smul_right, Measure.prod_sum_right]

/-- Averaging the ordered speed tuple produces exactly the ideal joint law. -/
theorem jointLaw_eq_mixture (speed : I → ℝ) :
    (productPositions I).prod (idealDirectionLaw speed) =
      (Fintype.card (Equiv.Perm I) : ℝ≥0∞)⁻¹ • ∑ p, classLaw speed p := by
  let m (p : Equiv.Perm I) := (Measure.pi (fun _ : I => angularHaar)).map (fromAngles speed p)
  have (p : Equiv.Perm I) : IsFiniteMeasure (m p) := by unfold m; infer_instance
  exact mixed_product (productPositions I) m _

/-- Null boundaries of canonical bins are null in every permutation component. -/
theorem class_frontier_null (speed : I → ℝ) (p : Equiv.Perm I)
    {B : Set (HyperbolicHost I × PiLp 2 (fun _ : I => ℂ))}
    (hn : ((productPositions I).prod (idealDirectionLaw speed)) (frontier B) = 0) :
    classLaw speed p (frontier B) = 0 := by
  rw [jointLaw_eq_mixture, Measure.smul_apply, smul_eq_mul, mul_eq_zero] at hn
  have hsum := hn.resolve_left (ENNReal.inv_ne_zero.mpr (by simp))
  rw [Measure.finsetSum_apply, Finset.sum_eq_zero_iff] at hsum
  exact hsum p (Finset.mem_univ _)

end Cover.Frame

end BorderVNP
end Computability
end OAI

import OAI.Computability.BorderVNP.CoverSiteRounding
import OAI.Computability.BorderVNP.CoverFramePositionLaw
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Ideal position probabilities for site rounding

Take the normalized hyperbolic area of the canonical base tile in every
coordinate. One open null-boundary test contains all failures of simultaneous
site rounding and has probability at most a constant times the segment length.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover

open Set Finset MeasureTheory UpperHalfPlane
open scoped ENNReal

/-- The ideal position marginal in the product host, after returning each coordinate
to the base tile by its integral address. -/
noncomputable def productPositionLaw (q : ℕ) : Measure (Fin q → ℍ) :=
  Measure.pi fun _ => Frame.positionLaw 0

/-- A common linear probability estimate for every quotient level and every endpoint
pair in the product. The number of surface factors enters only by the union bound. -/
theorem product_rounding_test : ∃ C ≥ (0 : ℝ), ∀ (q : ℕ) (r : ℝ), 0 < r → 4*r ≤ 1 →
    ∃ T : Set (Fin q → ℍ), IsOpen T ∧ productPositionLaw q (frontier T) = 0 ∧
      productPositionLaw q T ≤ ENNReal.ofReal (q*C*r) ∧
      ∀ d (x y : Fin q → Surface (d+1)), (∀ i, dist (x i) (y i) ≤ r) →
        (fun i => roundedSite d (x i)) ≠ (fun i => roundedSite d (y i)) →
        (fun i => relativePosition d (x i)) ∈ T := by
  obtain ⟨K,hK,hT⟩ := surface_rounding_test
  let m := ((volume : Measure ℍ) (planeTile 0))⁻¹
  have hm : m ≠ ∞ := ENNReal.inv_ne_top.mpr (Frame.planeTile_volume_ne_zero 0)
  refine ⟨m.toReal*K,by positivity,?_⟩
  intro q r hr hr'
  obtain ⟨S,ho,hn,hp,hc⟩ := hT r hr hr'
  let E (i : Fin q) := (Function.eval i : (Fin q → ℍ) → ℍ) ⁻¹' S
  let T := ⋃ i, E i
  have he (i : Fin q) : MeasurePreserving (Function.eval i) (productPositionLaw q) (Frame.positionLaw 0) :=
    measurePreserving_eval (fun _ => Frame.positionLaw 0) i
  have hnull : Frame.positionLaw 0 (frontier S) = 0 := by
    apply le_zero_iff.mp
    exact (Frame.positionLaw_le 0 _).trans (by simp [hn])
  have hmass : Frame.positionLaw 0 S ≤ ENNReal.ofReal (m.toReal*K*r) := by
    calc
      Frame.positionLaw 0 S ≤ m * volume S := Frame.positionLaw_le 0 S
      _ ≤ m * ENNReal.ofReal (K*r) := by gcongr
      _ = ENNReal.ofReal (m.toReal*K*r) := by
        rw [mul_assoc, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hm]
  refine ⟨T,isOpen_iUnion (fun i => ho.preimage (continuous_apply i)),?_,?_,?_⟩
  · have hsub : frontier T ⊆ ⋃ i, frontier (E i) := by
      simpa [T] using (Finset.univ : Finset (Fin q)).frontier_biUnion_subset E
    apply measure_mono_null hsub (measure_iUnion_null fun i => ?_)
    have hfront : frontier (E i) ⊆ (Function.eval i : (Fin q → ℍ) → ℍ) ⁻¹' frontier S :=
      (show Continuous (Function.eval i : (Fin q → ℍ) → ℍ) from continuous_apply i).frontier_preimage_subset S
    apply measure_mono_null hfront
    rw [(he i).measure_preimage isClosed_frontier.measurableSet.nullMeasurableSet, hnull]
  · calc
      _ ≤ ∑ i : Fin q, productPositionLaw q (E i) := measure_iUnion_fintype_le _ _
      _ ≤ ∑ _ : Fin q, ENNReal.ofReal (m.toReal*K*r) := Finset.sum_le_sum fun i _ => by
        rw [(he i).measure_preimage ho.measurableSet.nullMeasurableSet]; exact hmass
      _ = _ := by simp [mul_assoc, ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  · intro d x y hxy hne
    obtain ⟨i,hi⟩ : ∃ i, roundedSite d (x i) ≠ roundedSite d (y i) := by
      by_contra! h
      exact hne (funext h)
    exact mem_iUnion.mpr ⟨i,hc d _ _ (hxy i) hi⟩

end Cover

end BorderVNP
end Computability
end OAI

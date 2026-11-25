import OAI.Computability.BorderVNP.CoverRelativePlacement
import OAI.Computability.BorderVNP.CoverFrameDisintegration
import OAI.Computability.BorderVNP.ShortenEpochDirichlet
import OAI.Computability.BorderVNP.CoverChartBins

/-!
# Recovering the actual relative frame from the quotient

The chosen representative lies over the exact position tile. On the image of
the tile interior the choice is locally continuous. This open set has full
quotient Haar mass, and its representative coordinates have the required
product law.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover.Frame

open UpperHalfPlane Set MeasureTheory Filter Hecke
open scoped Topology

/-- The tie-resolved representative of a frame coset. -/
noncomputable def quotientRepresentative : Cosets (lattice 1) → SL :=
  Quotient.lift relativeFrame fun x y h => by
    obtain ⟨b,hb⟩ := QuotientGroup.rightRel_apply.mp h
    have he : y = gammaSL 1 b * x := by rw [hb]; group
    rw [he,relativeFrame_translate]

/-- A representative already over the chosen base tile is fixed by normalization. -/
theorem relativeFrame_fixed {x : SL} (hx : x • I ∈ planeTile 0) : relativeFrame x = x := by
  have h1 : toBaseTile (x • I) = 1 := (existsUnique_mem_planeTile 0 _).unique
    (toBaseTile_mem _) (by simpa using hx)
  simp [relativeFrame,h1]

/-- The representative is Borel on the whole quotient, including the tie choices. -/
theorem quotientRepresentative_measurable : Measurable quotientRepresentative := by
  apply measurable_from_quotient.mpr
  change Measurable relativeFrame
  apply Measurable.mul _ measurable_id
  let A (b : gamma 1) := {x : SL | gammaSL 1 b • (x • I) ∈ planeTile 0}
  have hA (b : gamma 1) : MeasurableSet (A b) := (planeTile_measurable 0).preimage
    (show Continuous (fun x : SL => gammaSL 1 b • (x • I)) by fun_prop).measurable
  intro S hS
  have h : (fun x : SL => gammaSL 1 (toBaseTile (x • I))) ⁻¹' S =
      ⋃ b : {b : gamma 1 // gammaSL 1 b ∈ S}, A b := by
    ext x
    constructor
    · intro hx
      exact mem_iUnion.mpr ⟨⟨toBaseTile (x • I),hx⟩,toBaseTile_mem _⟩
    · intro hx
      obtain ⟨b,hb⟩ := mem_iUnion.mp hx
      have he := (existsUnique_mem_planeTile 0 _).unique (toBaseTile_mem _) hb
      change gammaSL 1 (toBaseTile (x • I)) ∈ S
      rw [he]
      exact b.property
  change MeasurableSet ((fun x : SL => gammaSL 1 (toBaseTile (x • I))) ⁻¹' S)
  rw [h]
  exact MeasurableSet.iUnion fun b => hA b

/-- Representative coordinates vary continuously at every frame over the tile interior. -/
theorem quotientRepresentative_continuousAt {x : SL} (hx : x • I ∈ interior (planeTile 0)) :
    ContinuousAt quotientRepresentative (coset (lattice 1) x) := by
  apply (coset_openQuotient (lattice 1)).continuousAt_comp_iff.mp
  apply continuousAt_id.congr
  filter_upwards [(show Continuous (fun x : SL => x • I) by fun_prop).continuousAt
    (isOpen_interior.mem_nhds hx)] with y hy
  exact (relativeFrame_fixed (interior_subset hy)).symm

/-- The normalized quotient law over the base position tile. -/
noncomputable def baseHaar : Measure (Cosets (lattice 1)) :=
  tileHaar (lattice 1) (((volume : Measure UpperHalfPlane) (planeTile 0))⁻¹ • frameVolume)
    (positionFrameTile 0)

instance baseHaar_probability : IsProbabilityMeasure baseHaar :=
  tileHaar_probability 1 _ (positionFrameTile_mass 0)

instance baseHaar_openPos : baseHaar.IsOpenPosMeasure := by
  have hn := Measure.IsHaarMeasure.smul frameVolume
    (ENNReal.inv_ne_zero.mpr (planeTile_volume_ne_top 0))
    (ENNReal.inv_ne_top.mpr (planeTile_volume_ne_zero 0))
  exact tileHaar_openPos 1 _ (exact_position_frame_tile 0).1 (exact_position_frame_tile 0).2

private theorem positionLaw_ae_interior : ∀ᵐ p ∂positionLaw 0, p ∈ interior (planeTile 0) := by
  have hmem : ∀ᵐ p ∂positionLaw 0, p ∈ planeTile 0 :=
    Measure.ae_smul_measure (ae_restrict_mem (planeTile_measurable 0)) _
  have hnull : positionLaw 0 (frontier (planeTile 0)) = 0 := by
    apply le_antisymm _ bot_le
    apply (positionLaw_le 0 _).trans
    simp [Measure.smul_apply,Epoch.planeTile_frontier_null]
  filter_upwards [hmem,measure_eq_zero_iff_ae_notMem.mp hnull] with p hp hn
  exact (mem_interior_iff_notMem_frontier hp).mpr hn

/-- Normalization is continuous almost everywhere for the actual invariant quotient measure. -/
theorem quotientRepresentative_ae_continuous : ∀ᵐ x ∂baseHaar, ContinuousAt quotientRepresentative x := by
  let U := coset (lattice 1) '' (fun x : SL => x • I) ⁻¹' interior (planeTile 0)
  have hu : IsOpen U := (coset_openQuotient (lattice 1)).isOpenMap _
    (isOpen_interior.preimage (by fun_prop))
  have h : ∀ᵐ x ∂baseHaar, x ∈ U := by
    rw [baseHaar,quotient_frame_disintegration]
    apply (ae_map_iff ((coset_openQuotient (lattice 1)).continuous.comp frameCoordinates.symm.continuous).measurable.aemeasurable (p := fun q => q ∈ U) hu.measurableSet).mpr
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae positionLaw_ae_interior] with p hp
    refine ⟨frameCoordinates.symm p,?_,rfl⟩
    change (p.1.toSL2R * spin p.2) • I ∈ interior (planeTile 0)
    simpa [mul_smul,spin_fixes_I] using hp
  filter_upwards [h] with q hq
  obtain ⟨x,hx,rfl⟩ := hq
  exact quotientRepresentative_continuousAt hx

/-- Recovering position and rotation from a random quotient frame gives exactly
the independent normalized position and angular Haar laws. -/
theorem quotient_coordinates_preserving :
    MeasurePreserving (frameCoordinates ∘ quotientRepresentative) baseHaar
      ((positionLaw 0).prod Epoch.angularHaar) := by
  refine ⟨frameCoordinates.continuous.measurable.comp quotientRepresentative_measurable,?_⟩
  rw [baseHaar,quotient_frame_disintegration,Measure.map_map
    (frameCoordinates.continuous.measurable.comp quotientRepresentative_measurable)
    ((coset_openQuotient _).continuous.comp frameCoordinates.symm.continuous).measurable]
  have he : (frameCoordinates ∘ quotientRepresentative) ∘ (coset (lattice 1) ∘ frameCoordinates.symm)
      =ᵐ[(positionLaw 0).prod Epoch.angularHaar] id := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae positionLaw_ae_interior] with p hp
    change frameCoordinates (relativeFrame (frameCoordinates.symm p)) = p
    rw [relativeFrame_fixed, frameCoordinates.apply_symm_apply]
    change (p.1.toSL2R * spin p.2) • I ∈ planeTile 0
    simpa [mul_smul,spin_fixes_I] using interior_subset hp
  rw [Measure.map_congr he, Measure.map_id]

end Cover.Frame

end BorderVNP
end Computability
end OAI

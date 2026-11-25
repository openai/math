import OAI.Computability.BorderVNP.CoverFrameQuotientTopology
import OAI.Computability.BorderVNP.CoverLorentzTile
import OAI.Computability.BorderVNP.CoverHeckeCorrespondenceHaar
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-! # Normalized Haar measure with full support on the quaternion frame quotient -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover.Frame

open MeasureTheory Matrix Set Hecke
open scoped ENNReal Pointwise

/-- The normalized measure of a tile induces a probability measure on frame cosets. -/
theorem tileHaar_probability (l : ℕ) (μ : Measure SL) {D : Set SL} (hmass : μ D = 1) :
    IsProbabilityMeasure (tileHaar (frameGroup l) μ D) := by
  constructor
  have hq : Measurable (coset (frameGroup l)) :=
    measurable_quotient_mk' (s := QuotientGroup.rightRel (frameGroup l))
  simp [tileHaar, Measure.map_apply hq, hmass]

private theorem preimage_invariant (l : ℕ) (U : Set (Cosets (frameGroup l)))
    (a : frameGroup l) : a • (coset (frameGroup l) ⁻¹' U) = coset (frameGroup l) ⁻¹' U := by
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  change coset (frameGroup l) ((a : SL)⁻¹ * x) ∈ U ↔ coset (frameGroup l) x ∈ U
  have e : coset (frameGroup l) ((a : SL)⁻¹ * x) = coset (frameGroup l) x := by
    apply Quotient.sound
    apply QuotientGroup.rightRel_apply.mpr
    simp
  rw [e]

/-- Every nonempty open set of frames has positive measure, for any Borel exact tile and
any nonzero Haar normalization on the ambient group. -/
theorem tileHaar_openPos (l : ℕ) (μ : Measure SL) [μ.IsHaarMeasure] {D : Set SL}
    (hD : MeasurableSet D) (hd : ExactTile (frameGroup l) D) :
    (tileHaar (frameGroup l) μ D).IsOpenPosMeasure := by
  constructor
  intro U hU hne hz
  let A := coset (frameGroup l) ⁻¹' U
  have hA : IsOpen A := hU.preimage (coset_openQuotient _).continuous
  have hn : A.Nonempty := hne.preimage (coset_openQuotient _).surjective
  apply hA.measure_ne_zero μ hn
  have hfund : IsFundamentalDomain (frameGroup l) D μ := .mk' hD.nullMeasurableSet hd
  apply hfund.measure_zero_of_invariant A (preimage_invariant l U)
  have hq : Measurable (coset (frameGroup l)) :=
    measurable_quotient_mk' (s := QuotientGroup.rightRel (frameGroup l))
  change (μ.restrict D).map (coset (frameGroup l)) U = 0 at hz
  rw [Measure.map_apply hq hU.measurableSet] at hz
  change (μ.restrict D) A = 0 at hz
  rwa [Measure.restrict_apply hA.measurableSet] at hz

/-- A normalized Haar measure and exact Borel tile for every level of the compact frame
quotient. In particular all measure hypotheses of the finite Hecke correspondence and its
uniform convergence theorem are available at the base level. -/
theorem exists_normalized_frameHaar (l : ℕ) :
    ∃ (μ : Measure SL) (D : Set SL), μ.IsHaarMeasure ∧ MeasurableSet D ∧
      ExactTile (frameGroup l) D ∧ μ D = 1 ∧ IsProbabilityMeasure (tileHaar (frameGroup l) μ D) ∧
      (tileHaar (frameGroup l) μ D).IsOpenPosMeasure := by
  obtain ⟨K,D,hK,hDK,hD,hd⟩ := exists_measurable_frame_tile l
  let μ : Measure SL := Measure.haar
  have hfund : IsFundamentalDomain (frameGroup l) D μ := .mk' hD.nullMeasurableSet hd
  have hp : μ D ≠ 0 := hfund.measure_ne_zero (NeZero.ne μ)
  have hf : μ D ≠ ∞ := ((measure_mono hDK).trans_lt (hK.measure_lt_top (μ := μ))).ne
  let ν := (μ D)⁻¹ • μ
  have hν : ν.IsHaarMeasure := Measure.IsHaarMeasure.smul μ
    (ENNReal.inv_ne_zero.mpr hf) (ENNReal.inv_ne_top.mpr hp)
  have hm : ν D = 1 := by
    simpa only [ν, Measure.smul_apply, smul_eq_mul] using ENNReal.inv_mul_cancel hp hf
  exact ⟨ν, D, hν, hD, hd, hm, tileHaar_probability l ν hm, tileHaar_openPos l ν hD hd⟩

end Cover.Frame

end BorderVNP
end Computability
end OAI

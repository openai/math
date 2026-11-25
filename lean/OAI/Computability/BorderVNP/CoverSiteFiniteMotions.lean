import OAI.Computability.BorderVNP.CoverSiteRoundingLaw
import OAI.Computability.BorderVNP.CoverRelativeChart
import OAI.Computability.BorderVNP.CoverFiniteMotions
import OAI.Computability.BorderVNP.CoverLorentzMotion

/-!
# Finite rational motions for the last rounding of an epoch

For each finite collection of positive lengths, use one rational table of
quaternion motions. Uniform frame mixing controls the open boundary test at
each length. Testing the **actual moved endpoints** against that event bounds
the chance that their rounded sites differ. The coefficient of the length
bound depends only on the base tile.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover

open BorderVNP.Cover.Frame Hecke MeasureTheory Finset Filter Set UpperHalfPlane
open scoped Topology ENNReal BoundedContinuousFunction

/-- Indicator for a wire remaining nonlocal after rounding. -/
noncomputable def roundingFailure (d : ℕ) (x y : Surface (d+1)) : ℝ := by
  classical
  exact if roundedSite d x = roundedSite d y then 0 else 1

private noncomputable def chartPosition (q : Cosets (lattice 1)) : ℍ :=
  (frameCoordinates (quotientRepresentative q)).1

private theorem chartPosition_preserving :
    MeasurePreserving chartPosition baseHaar (positionLaw 0) :=
  (measurePreserving_fst (μ := positionLaw 0) (ν := Epoch.angularHaar)).comp quotient_coordinates_preserving

private theorem chartPosition_continuous : ∀ᵐ q ∂baseHaar, ContinuousAt chartPosition q := by
  filter_upwards [quotientRepresentative_ae_continuous] with q hq
  exact (frameCoordinates.continuous.continuousAt.comp hq).fst

private theorem chartPosition_site (d : ℕ) (g : SL) (x : ℍ) :
    chartPosition (coset (lattice 1) (g*x.toSL2R)) =
      relativePosition d (projectPoint (d+1) (g • x)) := by
  change (gammaSL 1 (toBaseTile ((g*x.toSL2R) • I)) * (g*x.toSL2R)) • I =
    gammaSL 1 (toBaseTile (g • x)) • (g • x)
  simp [mul_smul]

private theorem positive_tolerance {J : Type*} [Fintype J] (r : J → ℝ) (h : ∀ j, 0 < r j) :
    ∃ δ > (0:ℝ), ∀ j, δ ≤ r j := by
  classical
  let s : Finset ℝ := insert (1 : ℝ) (Finset.univ.image r)
  have hn : s.Nonempty := ⟨1,Finset.mem_insert_self ..⟩
  refine ⟨s.min' hn,?_,fun j => min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem r (Finset.mem_univ j)))⟩
  obtain h₁ | h₂ := Finset.mem_insert.mp (s.min'_mem hn)
  · rw [h₁]; norm_num
  · obtain ⟨j,_,hj⟩ := Finset.mem_image.mp h₂
    exact hj ▸ h j

/-- One finite rational motion table for a list of segment lengths. In every deeper
cover and for every pair of endpoints at the listed distance or less, the weight of
motions yielding distinct sites is at most the same host constant times the length. -/
theorem finite_rounding_motions : ∃ C ≥ (0:ℝ), ∀ {J : Type} [Fintype J] (r : J → ℝ),
    (∀ j, 0 < r j) → (∀ j, 4*r j ≤ 1) →
    ∃ (a m : ℕ) (w : Fin m → ℚ) (u : Fin m → SL) (hclear : ∀ i, Clears (u i) a),
      (∀ i, 0 < w i) ∧ (∑ i, w i) = 1 ∧
      ∀ j d (x y : Surface (d+1+2*a)), dist x y ≤ r j →
        ∑ i, (w i : ℝ) * roundingFailure d (surfaceMotion (hclear i) (d+1) x)
          (surfaceMotion (hclear i) (d+1) y) ≤ C*r j := by
  classical
  obtain ⟨K,hK,hT⟩ := surface_rounding_test
  let A := ((volume : Measure ℍ) (planeTile 0))⁻¹
  have hA : A ≠ ∞ := ENNReal.inv_ne_top.mpr (planeTile_volume_ne_zero 0)
  let C := A.toReal*K
  have hC : 0 ≤ C := mul_nonneg ENNReal.toReal_nonneg hK
  refine ⟨C+1,by positivity,?_⟩
  intro J _ r hr hsmall
  choose S hopen hnull hmass hcover using fun j => hT (r j) (hr j) (hsmall j)
  let B (j : J) := chartPosition ⁻¹' S j
  have hb (j : J) : MeasurableSet (B j) := chartPosition_preserving.measurable (hopen j).measurableSet
  have hfront (j : J) : baseHaar (frontier (B j)) = 0 := by
    apply CoverFrameMixing.chart_frontier_null chartPosition_preserving chartPosition_continuous
    apply le_zero_iff.mp
    exact (positionLaw_le 0 _).trans (by simp [hnull])
  have hm (j : J) : baseHaar.real (B j) ≤ C*r j := by
    have hx := chartPosition_preserving.measure_preimage (hopen j).measurableSet.nullMeasurableSet
    have hm' : baseHaar (B j) ≤ ENNReal.ofReal (C*r j) := by
      calc
        _ = positionLaw 0 (S j) := hx
        _ ≤ A * volume (S j) := positionLaw_le 0 _
        _ ≤ A * ENNReal.ofReal (K*r j) := by gcongr; exact hmass j
        _ = _ := by rw [show C*r j = A.toReal*(K*r j) by dsimp [C]; ring,
          ENNReal.ofReal_mul ENNReal.toReal_nonneg,ENNReal.ofReal_toReal hA]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hm').trans (by rw [ENNReal.toReal_ofReal (mul_nonneg hC (hr j).le)])
  obtain ⟨δ,hδ,hle⟩ := positive_tolerance r hr
  let I := Cosets (intersection (lattice 1) elliptic)
  have : Nonempty I := ⟨coset _ 1⟩
  have : Finite I := finite_elliptic_indices.1
  have : Finite (Cosets (intersection (lattice 1) elliptic⁻¹)) := finite_elliptic_indices.2
  let : Fintype I := Fintype.ofFinite _
  let : Fintype (Cosets (intersection (lattice 1) elliptic⁻¹)) := Fintype.ofFinite _
  have hstat (f : Cosets (lattice 1) →ᵇ ℝ) :
      ∫ x, operator (lattice 1) elliptic f x ∂baseHaar = ∫ x, f x ∂baseHaar := by
    have hi : Integrable f baseHaar := f.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
    exact Hecke.integral_average (lattice 1) _ elliptic (exact_position_frame_tile 0).1 (exact_position_frame_tile 0).2
      (positionFrameTile_mass 0) _ f.continuous.measurable hi
  have hden : Dense (Subgroup.closure ((lattice 1 : Set SL) ∪ {elliptic}) : Set SL) := by
    simpa [Set.union_comm, Set.singleton_union] using dense_generated
  obtain ⟨n,hn⟩ := (finite_frame_bins (lattice 1) elliptic baseHaar hstat hden B hb hfront hδ).exists
  let e := Fintype.equivFin (Samples I n)
  let v (s : Samples I n) := motion (step (lattice 1) elliptic) s.1.val s.2
  have hv (s : Samples I n) : Clears (v s) n := (clears_motion _ _).mono (Nat.le_of_lt_succ s.1.isLt)
  refine ⟨n,_,weight I n ∘ e.symm,v ∘ e.symm,fun i => hv _,fun i => weight_pos _ _,?_,?_⟩
  · exact (e.symm.sum_comp (weight I n)).trans (sum_weight _)
  · intro j d x y hxy
    rcases x with ⟨x⟩
    have hs (s : Samples I n) : roundingFailure d (surfaceMotion (hv s) (d+1) (projectPoint _ x))
        (surfaceMotion (hv s) (d+1) y) ≤ (B j).indicator (fun _ => (1:ℝ)) (coset _ (v s*x.toSL2R)) := by
      by_cases he : roundedSite d (surfaceMotion (hv s) (d+1) (projectPoint _ x)) =
          roundedSite d (surfaceMotion (hv s) (d+1) y)
      · simp [roundingFailure,he,Set.indicator]; split <;> norm_num
      · have hb' : coset (lattice 1) (v s*x.toSL2R) ∈ B j := by
          change chartPosition (coset (lattice 1) (v s*x.toSL2R)) ∈ S j
          rw [chartPosition_site d]
          apply hcover j d _ (surfaceMotion (hv s) (d+1) y)
          · exact (surfaceMotion_dist_le (hv s) (d+1) (projectPoint _ x) y).trans hxy
          · exact he
        simp [roundingFailure,he,Set.indicator_of_mem hb']
    have hmean := (abs_lt.mp (hn j x.toSL2R)).2
    have hsum : (∑ s : Samples I n, (weight I n s : ℝ) *
        roundingFailure d (surfaceMotion (hv s) (d+1) (projectPoint _ x)) (surfaceMotion (hv s) (d+1) y))
        ≤ wordMean (lattice 1) elliptic n x.toSL2R ((B j).indicator (fun _ => (1:ℝ))) :=
      sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hs s) (by exact_mod_cast (weight_pos n s).le)
    have reindex := e.symm.sum_comp (fun s => (weight I n s : ℝ) *
      roundingFailure d (surfaceMotion (hv s) (d+1) (projectPoint _ x)) (surfaceMotion (hv s) (d+1) y))
    apply reindex.trans_le
    linarith [hle j,hm j]

end Cover

end BorderVNP
end Computability
end OAI

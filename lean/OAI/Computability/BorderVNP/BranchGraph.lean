import OAI.Computability.BorderVNP.BranchCurvePlace
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# A finite parameter chart above each boundary value

Proposition 9.2 closes the graph of the coefficient map in projective parameter space
times affine output space. The valuative description yields its nonempty fiber over a
boundary value directly. Choose a largest homogeneous parameter in the valuation and
divide all homogeneous coordinates by it. The resulting chart entries and all outputs
lie in the same valuation ring. The residue point gives a proper ideal of the graph,
and the Nullstellensatz supplies a point of this fiber over the original closed field.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

open MvPolynomial

/-- Homogeneous coordinates of the generic point of parameter space. -/
noncomputable def homogeneousParameters (σ K : Type*) [Field K] :
    Option σ → ParameterField σ K :=
  fun j => j.elim 1 (fun i => algebraMap _ _ (X i : MvPolynomial σ K))

/-- The chart of the graph is defined by all relations on the ratios of homogeneous
parameters and the generic coefficient outputs. One chart coordinate is identically one. -/
noncomputable def graphChartMap {σ ι K : Type*} [Field K] (Y : ι → MvPolynomial σ K)
    (k : Option σ) : MvPolynomial (Option σ ⊕ ι) K →+* ParameterField σ K :=
  eval₂Hom ((genericTable Y).comp C)
    (Sum.elim (fun j => homogeneousParameters σ K j / homogeneousParameters σ K k)
      (fun i => genericTable Y (X i)))

/-- A valuation chooses a standard projective chart in which all parameters are regular. -/
theorem exists_chart_in_valuation {σ L : Type*} [Finite σ] [Field L] (V : ValuationSubring L)
    (u : Option σ → L) (hu : u none = 1) :
    ∃ k, u k ≠ 0 ∧ ∀ j, u j / u k ∈ V := by
  classical
  let := Fintype.ofFinite σ
  obtain ⟨k, _, hk⟩ := Finset.univ.exists_max_image (V.valuation ∘ u) Finset.univ_nonempty
  have h : 1 ≤ V.valuation (u k) := by simpa [hu] using hk none (Finset.mem_univ _)
  have hp : 0 < V.valuation (u k) := zero_lt_one.trans_le h
  refine ⟨k, fun hz => ?_, fun j => ?_⟩
  · simp [hz] at hp
  · rw [← V.valuation_le_one_iff, map_div₀, div_le_one₀ hp]
    exact hk j (Finset.mem_univ _)

/-- Above a boundary output there is a point on the closed graph in some standard
projective chart. The point solves every relation on that chart, has its chosen
chart coordinate equal to one, and has precisely the prescribed output coordinates. -/
theorem exists_graphChart_point {σ ι K : Type*} [Field K] [IsAlgClosed K] [Finite σ] [Finite ι]
    (Y : ι → MvPolynomial σ K) (c : ι → K)
    (hc : c ∈ imageClosure (Set.range (fun a : σ → K => fun i => eval a (Y i)))) :
    ∃ (k : Option σ) (z : Option σ → K), homogeneousParameters σ K k ≠ 0 ∧ z k = 1 ∧
      Sum.elim z c ∈ zeroLocus K (RingHom.ker (graphChartMap Y k)) := by
  classical
  obtain ⟨V, hV, hm⟩ := (mem_imageClosure_iff_valuation Y c).mp hc
  let u := homogeneousParameters σ K
  obtain ⟨k, hk, hu⟩ := exists_chart_in_valuation V u rfl
  let f := genericTable Y
  let scalar : K →+* V := (f.comp C).codRestrict V.toSubring fun a => hV ⟨C a, rfl⟩
  let zy : Option σ ⊕ ι → V :=
    Sum.elim (fun j => ⟨u j / u k, hu j⟩) (fun i => ⟨f (X i), hV ⟨X i, rfl⟩⟩)
  let lift := eval₂Hom scalar zy
  have hh : V.subtype.comp lift = graphChartMap Y k := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, lift, graphChartMap, eval₂Hom_C]
      rfl
    · intro a
      simp only [RingHom.comp_apply, lift, graphChartMap, eval₂Hom_X']
      cases a <;> rfl
  let res := (IsLocalRing.residue V).comp lift
  obtain ⟨M, hM, hRM⟩ := (RingHom.ker res).exists_le_maximal (RingHom.ker_ne_top res)
  obtain ⟨x, hx⟩ := eq_vanishingIdeal_singleton_of_isMaximal K hM
  have hex (P : MvPolynomial (Option σ ⊕ ι) K) (hP : res P = 0) : aeval x P = 0 := by
    apply (mem_vanishingIdeal_singleton_iff x P).mp
    rw [← hx]
    exact hRM hP
  have kernel (P : MvPolynomial (Option σ ⊕ ι) K) (hP : graphChartMap Y k P = 0) :
      res P = 0 := by
    have hz : lift P = 0 := Subtype.ext (by change (V.subtype.comp lift) P = 0; rwa [hh])
    simp [res, hz]
  have hfirst : x (.inl k) = 1 := by
    have h := hex (X (.inl k) - 1) (kernel _ (by
      rw [map_sub, map_one]; unfold graphChartMap; rw [eval₂Hom_X'];
      exact sub_eq_zero.mpr (div_self hk)))
    simpa [sub_eq_zero] using h
  have hy (i : ι) : x (.inr i) = c i := by
    have h := hex (X (.inr i) - C (c i)) (by
      change IsLocalRing.residue V (lift _) = 0
      rw [IsLocalRing.residue_eq_zero_iff]
      apply V.coe_mem_nonunits_iff.mp
      change V.subtype.comp lift _ ∈ V.nonunits
      rw [hh]
      rw [map_sub]; unfold graphChartMap; rw [eval₂Hom_X', eval₂Hom_C]
      simpa only [eval_X, Sum.elim_inr, RingHom.comp_apply] using hm (X i))
    simpa [sub_eq_zero] using h
  refine ⟨k, x ∘ Sum.inl, hk, hfirst, ?_⟩
  have hxzc : Sum.elim (x ∘ Sum.inl) c = x := by
    funext j
    cases j with
    | inl i => rfl
    | inr i => exact (hy i).symm
  rw [hxzc]
  exact fun P hP => hex P (kernel P hP)

end Branch

end BorderVNP
end Computability
end OAI

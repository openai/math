import OAI.Computability.BorderVNP.CoverHeckeCorrespondenceDomain
import OAI.Computability.BorderVNP.CoverHeckeCorrespondenceWords
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Haar stationarity of the finite Hecke correspondence

For a Borel tile with boundary choices, the normalized quotient Haar measure is
the image of ambient Haar restricted to the tile. The integral comparison uses
the two explicit domains for the subgroup conjugated by `z`; it does not
require measure preservation of any individual branch on the base quotient.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Hecke

open MeasureTheory Finset Set
open scoped ENNReal Pointwise

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
    (Γ : Subgroup G) (μ : Measure G) [μ.IsMulLeftInvariant]

private theorem integral_expanded (S : Subgroup Γ) [Fintype (Cosets S)]
    {D : Set G} (hD : MeasurableSet D) (hd : ExactTile Γ D) (f : G → ℝ≥0∞) :
    ∫⁻ x in expandedTile Γ S D, f x ∂μ =
      ∑ i : Cosets S, ∫⁻ x in D, f ((i.out : G) * x) ∂μ := by
  rw [expandedTile, lintegral_iUnion (fun i : Cosets S => hD.const_smul (i.out : G))
    (disjoint_expandedTile Γ S hd), tsum_fintype]
  apply sum_congr rfl
  intro i _
  exact ((measurePreserving_smul (i.out : G) μ).setLIntegral_comp_emb
    (measurableEmbedding_const_smul _) f D).symm

variable (z : G) [Countable Γ] [Fintype (Cosets (intersection Γ z))]
    [Fintype (Cosets (intersection Γ z⁻¹))]

private theorem integral_correspondence {D : Set G} (hD : MeasurableSet D)
    (hd : ExactTile Γ D) (f : G → ℝ≥0∞) (hf : ∀ (a : Γ) x, f ((a : G) * x) = f x) :
    ∑ i : Cosets (intersection Γ z), ∫⁻ x in D, f (step Γ z i * x) ∂μ =
      (Fintype.card (Cosets (intersection Γ z⁻¹)) : ℝ≥0∞) * ∫⁻ x in D, f x ∂μ := by
  let E := expandedTile Γ (intersection Γ z) D
  let E' := expandedTile Γ (intersection Γ z⁻¹) D
  have hi := integral_expanded Γ μ (intersection Γ z) hD hd (fun x => f (z * x))
  have ht : ∫⁻ x in E, f (z * x) ∂μ = ∫⁻ x in z • E, f x ∂μ :=
    (measurePreserving_smul z μ).setLIntegral_comp_emb (measurableEmbedding_const_smul _) f E
  have he : ∫⁻ x in z • E, f x ∂μ = ∫⁻ x in E', f x ∂μ :=
    (fundamental_translatedTile Γ z hD hd μ).setLIntegral_eq
      (fundamental_expandedTile Γ _ hD hd μ) f (fun a x => hf a.val x)
  have hj := integral_expanded Γ μ (intersection Γ z⁻¹) hD hd f
  simpa [step, mul_assoc, hf, E, E', nsmul_eq_mul] using hi.symm.trans (ht.trans (he.trans hj))

/-- Conjugate subgroups in the Hecke correspondence have equal indices in the lattice.
Here the ambient Haar measure is scaled to assign mass one to the base tile. -/
theorem card_intersection_inv {D : Set G} (hD : MeasurableSet D) (hd : ExactTile Γ D)
    (hn : μ D = 1) :
    Fintype.card (Cosets (intersection Γ z)) = Fintype.card (Cosets (intersection Γ z⁻¹)) := by
  have h := integral_correspondence Γ μ z hD hd (fun _ => 1) (fun _ _ => rfl)
  simpa [hn] using h

/-- Integrating the unnormalized Hecke sum over a fundamental domain multiplies the
integral of a nonnegative observable by the covering index. -/
theorem stationary_branch_integrals {D : Set G} (hD : MeasurableSet D)
    (hd : ExactTile Γ D) (hn : μ D = 1) (f : Cosets Γ → ℝ≥0∞) :
    ∑ i : Cosets (intersection Γ z), ∫⁻ x in D, f (branch Γ z x i) ∂μ =
      (Fintype.card (Cosets (intersection Γ z)) : ℝ≥0∞) * ∫⁻ x in D, f (coset Γ x) ∂μ := by
  simp_rw [branch_step]
  rw [card_intersection_inv Γ μ z hD hd hn]
  apply integral_correspondence Γ μ z hD hd (fun x => f (coset Γ x))
  intro a x
  apply congrArg f
  apply Quotient.sound
  apply QuotientGroup.rightRel_apply.mpr
  simp

/-- The Haar measure on the frame quotient obtained from a fundamental tile. -/
noncomputable def tileHaar (D : Set G) : Measure (Cosets Γ) :=
  (μ.restrict D).map (coset Γ)

/-- The finite branch images of a tile, counted with multiplicity, give exactly
the index times the quotient Haar measure. -/
theorem sum_map_branches {D : Set G} (hD : MeasurableSet D)
    (hd : ExactTile Γ D) (hn : μ D = 1) :
    ∑ i : Cosets (intersection Γ z), (μ.restrict D).map (fun x => branch Γ z x i) =
      Fintype.card (Cosets (intersection Γ z)) • tileHaar Γ μ D := by
  ext A hA
  have hc : Measurable (coset Γ) := measurable_quotient_mk' (s := QuotientGroup.rightRel Γ)
  have hb (i : Cosets (intersection Γ z)) : Measurable (fun x => branch Γ z x i) := by
    simp_rw [branch_step]
    exact hc.comp (measurable_const_mul _)
  have hm := stationary_branch_integrals Γ μ z hD hd hn (A.indicator (fun _ => 1))
  have measure_preimage (g : G → Cosets Γ) (hg : Measurable g) :
      (∫⁻ x in D, A.indicator (fun _ => (1 : ℝ≥0∞)) (g x) ∂μ) =
        μ.restrict D (g ⁻¹' A) := by
    have eqfn : (fun x => A.indicator (fun _ => (1 : ℝ≥0∞)) (g x)) =
        (g ⁻¹' A).indicator (fun _ => 1) := by
      ext x
      by_cases h : g x ∈ A <;> simp [Set.indicator, h]
    rw [eqfn, lintegral_indicator (hA.preimage hg)]
    simp
  rw [measure_preimage (coset Γ) hc] at hm
  simp_rw [measure_preimage (fun x => branch Γ z x _) (hb _)] at hm
  simpa [Measure.finsetSum_apply, Measure.map_apply, hb, hc, hA, tileHaar, Measure.smul_apply,
    nsmul_eq_mul] using hm

/-- Haar stationarity for the actual normalized real Hecke operator. -/
theorem integral_average {D : Set G} (hD : MeasurableSet D) (hd : ExactTile Γ D)
    (hn : μ D = 1) (f : Cosets Γ → ℝ) (hf : Measurable f)
    (hi : Integrable f (tileHaar Γ μ D)) :
    ∫ x, average Γ z f x ∂(tileHaar Γ μ D) = ∫ x, f x ∂(tileHaar Γ μ D) := by
  let I := Cosets (intersection Γ z)
  let ψ (i : I) (x : G) := branch Γ z x i
  let ν (i : I) := (μ.restrict D).map (ψ i)
  let m := tileHaar Γ μ D
  have hc : Measurable (coset Γ) := measurable_quotient_mk' (s := QuotientGroup.rightRel Γ)
  have hψ (i : I) : Measurable (ψ i) := by
    simp only [ψ, branch_step]
    exact hc.comp (measurable_const_mul _)
  have hmeas : Measurable (average Γ z f) := by
    apply measurable_from_quotient.mpr
    change Measurable (fun x => (Fintype.card I : ℝ)⁻¹ * ∑ i, f (ψ i x))
    exact measurable_const.mul (Finset.measurable_fun_sum _ (fun i _ => hf.comp (hψ i)))
  have hsum : ∑ i, ν i = (Fintype.card I : ℝ≥0∞) • m := by
    rw [Nat.cast_smul_eq_nsmul]
    exact sum_map_branches Γ μ z hD hd hn
  have hiν (i : I) : Integrable f (ν i) := by
    have h := hi.smul_measure (ENNReal.natCast_ne_top (Fintype.card I))
    change Integrable f ((Fintype.card I : ℝ≥0∞) • m) at h
    rw [← hsum, integrable_finsetSum_measure] at h
    exact h i (mem_univ i)
  have hind : Nonempty I := ⟨coset (intersection Γ z) 1⟩
  have hnI : (Fintype.card I : ℝ) ≠ 0 := by positivity
  change ∫ x, average Γ z f x ∂((μ.restrict D).map (coset Γ)) = ∫ x, f x ∂m
  rw [integral_map hc.aemeasurable hmeas.aestronglyMeasurable]
  change ∫ x in D, (Fintype.card I : ℝ)⁻¹ * ∑ i, f (ψ i x) ∂μ = _
  rw [integral_const_mul, integral_finsetSum (f := fun i x => f (ψ i x)) univ (fun i _ => (hiν i).comp_measurable (hψ i))]
  have hmap (i : I) : ∫ x in D, f (ψ i x) ∂μ = ∫ x, f x ∂(ν i) :=
    (integral_map (hψ i).aemeasurable (hiν i).aestronglyMeasurable).symm
  simp_rw [hmap]
  rw [← integral_finsetSum_measure (fun i _ => hiν i), hsum, integral_smul_measure]
  simp [hnI]

end Hecke

end BorderVNP
end Computability
end OAI

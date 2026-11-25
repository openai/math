import OAI.Computability.BorderVNP.CoverFrameBins
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi

/-!
# Independently moving the factors of the product host

The discrete law consists of genuine atoms at the images of a starting frame
under finite rational words. Its weak convergence is uniform in starting
frames. The product of independently sampled words converges weakly to the
product Haar law, which gives a simultaneous estimate on any finite collection
of continuity bins in the full product space.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Hecke

open BoundedContinuousFunction Filter Finset Set MeasureTheory
open scoped Topology ENNReal

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (Γ : Subgroup G) (z : G) [Fintype (Cosets (intersection Γ z))]
    [MeasurableSpace (Cosets Γ)]

/-- The finite atomic measure of rational motions of one specified frame. -/
noncomputable def wordLaw (n : ℕ) (x : G) : ProbabilityMeasure (Cosets Γ) :=
  ⟨∑ s : Samples (Cosets (intersection Γ z)) n,
      ENNReal.ofReal (weight _ n s) • Measure.dirac (coset Γ (motion (step Γ z) s.1 s.2 * x)),
    ⟨by
      have : Nonempty (Cosets (intersection Γ z)) := ⟨coset _ 1⟩
      simp only [Measure.finsetSum_apply, Measure.smul_apply, measure_univ,
        smul_eq_mul, mul_one]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun s _ => Rat.cast_nonneg.mpr (weight_pos n s).le)]
      have hs : (∑ s : Samples (Cosets (intersection Γ z)) n, (weight _ n s : ℝ)) = 1 := by
        exact_mod_cast sum_weight (I := Cosets (intersection Γ z)) n
      rw [hs, ENNReal.ofReal_one]⟩⟩

variable [OpensMeasurableSpace (Cosets Γ)]

omit [IsTopologicalGroup G] in
/-- Integrating a continuous observable against the word law gives its rational sample mean. -/
theorem integral_wordLaw (f : Cosets Γ →ᵇ ℝ) (n : ℕ) (x : G) :
    (∫ u, f u ∂(wordLaw Γ z n x).toMeasure) = wordMean Γ z n x f := by
  have : Nonempty (Cosets (intersection Γ z)) := ⟨coset _ 1⟩
  rw [wordLaw, ProbabilityMeasure.coe_mk, integral_finsetSum_measure]
  · simp only [wordMean, integral_smul_measure, integral_dirac' _ _ f.continuous.stronglyMeasurable,
      ENNReal.toReal_ofReal (Rat.cast_nonneg.mpr (weight_pos n _).le), smul_eq_mul]
  · intro s _
    exact (integrable_dirac' f.continuous.stronglyMeasurable (by simp)).smul_measure
      ENNReal.ofReal_ne_top

variable [CompactSpace (Cosets Γ)]
    (μ : Measure (Cosets Γ)) [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure]

/-- Weak convergence even if the starting frame varies arbitrarily with the sample length. -/
theorem wordLaw_tendsto {Y : Type*} {l : Filter Y} {N : Y → ℕ} (x : Y → G)
    (hN : Tendsto N l atTop)
    (hμ : ∀ f : Cosets Γ →ᵇ ℝ, (∫ y, operator Γ z f y ∂μ) = ∫ y, f y ∂μ)
    (hd : Dense (Subgroup.closure ((Γ : Set G) ∪ {z}) : Set G)) :
    Tendsto (fun y => wordLaw Γ z (N y) (x y)) l (𝓝 μ.toProbabilityMeasure) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  simp only [integral_wordLaw, ← mean_eq_wordMean]
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hN (Metric.tendsto_nhds.mp (frame_means_tendsto Γ z μ hμ hd f) ε hε)] with y hy
  exact lt_of_le_of_lt (BoundedContinuousFunction.dist_coe_le_dist
    (f := CoverFrameMixing.mean (operator Γ z) f (N y)) (g := const _ (∫ u, f u ∂μ))
    (coset Γ (x y))) hy

/-- Independent samples in all the factors of a product host. -/
noncomputable def productLaw {I : Type*} [Fintype I] (n : ℕ) (x : I → G) :
    ProbabilityMeasure (I → Cosets Γ) :=
  ProbabilityMeasure.pi (α := fun _ : I => Cosets Γ) (fun i : I => wordLaw Γ z n (x i))

private theorem product_tendsto {I : Type*} [Fintype I]
    [SecondCountableTopology (Cosets Γ)] [TopologicalSpace.PseudoMetrizableSpace (Cosets Γ)]
    (hμ : ∀ f : Cosets Γ →ᵇ ℝ, (∫ y, operator Γ z f y ∂μ) = ∫ y, f y ∂μ)
    (hd : Dense (Subgroup.closure ((Γ : Set G) ∪ {z}) : Set G)) :
    Tendsto (fun s : ℕ × (I → G) => productLaw Γ z s.1 s.2)
      ((atTop : Filter ℕ) ×ˢ (⊤ : Filter (I → G)))
      (𝓝 (ProbabilityMeasure.pi (α := fun _ : I => Cosets Γ) (fun _ : I => μ.toProbabilityMeasure))) := by
  let F := (atTop : Filter ℕ) ×ˢ (⊤ : Filter (I → G))
  have hcoord (i : I) : Tendsto (fun s : ℕ × (I → G) => wordLaw Γ z s.1 (s.2 i)) F
      (𝓝 μ.toProbabilityMeasure) :=
    wordLaw_tendsto Γ z μ (fun (s : ℕ × (I → G)) => s.2 i) tendsto_fst hμ hd
  have ht := tendsto_pi_nhds.mpr hcoord
  exact (ProbabilityMeasure.continuous_pi (α := fun _ : I => Cosets Γ)).continuousAt.tendsto.comp ht

/-- The joint error in any finite collection of product bins is uniformly small,
including bins that couple several coordinates. The product law corresponds
to independent choices for all the surface factors. -/
theorem product_bin_estimate {I J : Type*} [Fintype I] [Finite J]
    [SecondCountableTopology (Cosets Γ)] [TopologicalSpace.PseudoMetrizableSpace (Cosets Γ)]
    (hμ : ∀ f : Cosets Γ →ᵇ ℝ, (∫ y, operator Γ z f y ∂μ) = ∫ y, f y ∂μ)
    (hd : Dense (Subgroup.closure ((Γ : Set G) ∪ {z}) : Set G))
    (B : J → Set (I → Cosets Γ)) (hB : ∀ j, (Measure.pi (fun _ : I => μ)) (frontier (B j)) = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ j (x : I → G),
      |(productLaw Γ z n x).toMeasure.real (B j) -
        (Measure.pi (fun _ : I => μ)).real (B j)| < ε := by
  rw [Filter.eventually_all]
  intro j
  let L := (atTop : Filter ℕ) ×ˢ (⊤ : Filter (I → G))
  let target := ProbabilityMeasure.pi (α := fun _ : I => Cosets Γ) (fun _ : I => μ.toProbabilityMeasure)
  let law (s : ℕ × (I → G)) := productLaw Γ z s.1 s.2
  have ht : Tendsto law L (𝓝 target) :=
    product_tendsto Γ z μ hμ hd
  have he := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' ht (hB j)
  have hr := (ENNReal.continuousAt_toReal (measure_ne_top _ _)).tendsto.comp he
  have hab := Metric.tendsto_nhds.mp hr ε hε
  change {s : ℕ × (I → G) | dist ((law s).toMeasure (B j)).toReal (target.toMeasure (B j)).toReal < ε} ∈ L at hab
  exact (Filter.mem_prod_top.mp hab : ∀ᶠ n in atTop, ∀ x,
    dist ((law (n,x)).toMeasure (B j)).toReal (target.toMeasure (B j)).toReal < ε)

end Hecke

end BorderVNP
end Computability
end OAI

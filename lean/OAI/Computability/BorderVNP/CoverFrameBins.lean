import OAI.Computability.BorderVNP.CoverFrameConvergence
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-!
# One rational distribution for all the frame bins

At every sufficiently large Cesàro length the finite rational distribution
on words approximates the Haar masses of every set in a prescribed finite
family of Borel continuity sets, uniformly in the starting frame. The upper
estimate uses a continuous thickening of the closure. The same estimate for
the complement gives the lower estimate.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Hecke

open BoundedContinuousFunction Finset Filter MeasureTheory Set
open scoped Topology

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (Γ : Subgroup G) (z : G) [Fintype (Cosets (intersection Γ z))]

/-- Expectation over the actual finite rational word distribution. -/
noncomputable def wordMean (n : ℕ) (x : G) (f : Cosets Γ → ℝ) : ℝ :=
  ∑ s : Samples (Cosets (intersection Γ z)) n, (weight _ n s : ℝ) *
    f (coset Γ (motion (step Γ z) s.1 s.2 * x))

omit [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem wordMean_mono {f h : Cosets Γ → ℝ} (le : f ≤ h) (n : ℕ) (x : G) :
    wordMean Γ z n x f ≤ wordMean Γ z n x h := by
  have : Nonempty (Cosets (intersection Γ z)) := ⟨coset _ 1⟩
  apply sum_le_sum
  intro s _
  apply mul_le_mul_of_nonneg_left (le _) (Rat.cast_nonneg.mpr (weight_pos _ s).le)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem wordMean_compl (n : ℕ) (x : G) (B : Set (Cosets Γ)) :
    wordMean Γ z n x (Bᶜ.indicator (fun _ => 1)) + wordMean Γ z n x (B.indicator (fun _ => 1)) = 1 := by
  classical
  have hind (y : Cosets Γ) :
      Bᶜ.indicator (fun _ => (1 : ℝ)) y + B.indicator (fun _ => (1 : ℝ)) y = 1 := by
    by_cases h : y ∈ B <;> simp [Set.indicator, h]
  have : Nonempty (Cosets (intersection Γ z)) := ⟨coset _ 1⟩
  simp only [wordMean, ← sum_add_distrib, ← mul_add, hind, mul_one]
  exact_mod_cast sum_weight (I := Cosets (intersection Γ z)) n

variable [CompactSpace (Cosets Γ)]

/-- The bounded-function average and the finite rational word expectation agree at every frame. -/
theorem mean_eq_wordMean (f : Cosets Γ →ᵇ ℝ) (n : ℕ) (x : G) :
    CoverFrameMixing.mean (operator Γ z) f n (coset Γ x) = wordMean Γ z n x f := by
  have it (i : ℕ) : (fun y => (operator Γ z)^[i] f y) = (average Γ z)^[i] f := by
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply' (average Γ z)]
      exact congrArg (average Γ z) ih
  rw [wordMean, ← cesaro_words]
  simp only [CoverFrameMixing.mean, BoundedContinuousFunction.smul_apply, smul_eq_mul,
    BoundedContinuousFunction.sum_apply, sum_fin_eq_sum_range]
  congr 1
  apply sum_congr rfl
  intro j hj
  simpa only [dite_eq_left (mem_range.mp hj)] using congrFun (it j) (coset Γ x)

variable [MeasurableSpace (Cosets Γ)] [OpensMeasurableSpace (Cosets Γ)]
    (μ : Measure (Cosets Γ)) [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure]

private theorem eventually_upper [TopologicalSpace.PseudoMetrizableSpace (Cosets Γ)]
    (hμ : ∀ f : Cosets Γ →ᵇ ℝ, (∫ x, operator Γ z f x ∂μ) = ∫ x, f x ∂μ)
    (hdense : Dense (Subgroup.closure ((Γ : Set G) ∪ {z}) : Set G))
    (B : Set (Cosets Γ)) (hB : μ (frontier B) = 0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ x : G, wordMean Γ z n x (B.indicator (fun _ => 1)) < μ.real B + ε := by
  let := TopologicalSpace.pseudoMetrizableSpacePseudoMetric (Cosets Γ)
  have hpos (j : ℕ) : 0 < (1:ℝ) / (j+1) := by positivity
  let f (j : ℕ) : Cosets Γ →ᵇ ℝ := mkOfCompact
    ⟨fun y => (thickenedIndicator (hpos j) (closure B) y : ℝ),
      NNReal.continuous_coe.comp (thickenedIndicator (hpos j) (closure B)).continuous⟩
  have hconv : Tendsto (fun j => ∫ y, f j y ∂μ) atTop (𝓝 (μ.real B)) := by
    have h := tendsto_integral_thickenedIndicator_of_isClosed μ (isClosed_closure (s:=B))
      hpos tendsto_one_div_add_atTop_nhds_zero_nat
    rwa [Measure.real_def, measure_closure_of_null_frontier hB] at h
  obtain ⟨j,hj⟩ := (hconv.eventually_lt_const (by linarith : μ.real B < μ.real B + ε / 2)).exists
  have hdom : B.indicator (fun _ => (1:ℝ)) ≤ f j := by
    intro y
    by_cases hy : y ∈ B
    · rw [indicator_of_mem hy]
      exact NNReal.coe_le_coe.mpr (one_le_thickenedIndicator_apply _ (hpos j) (subset_closure hy))
    · rw [indicator_of_notMem hy]
      exact (thickenedIndicator (hpos j) (closure B) y).coe_nonneg
  have hnear := Metric.tendsto_nhds.mp (frame_means_tendsto Γ z μ hμ hdense (f j)) (ε/2) (by linarith)
  filter_upwards [hnear] with n hn x
  have h := lt_of_le_of_lt (BoundedContinuousFunction.dist_coe_le_dist (coset Γ x)) hn
  change dist (CoverFrameMixing.mean (operator Γ z) (f j) n (coset Γ x)) (∫ y, f j y ∂μ) < ε/2 at h
  rw [mean_eq_wordMean, Real.dist_eq] at h
  linarith [(abs_lt.mp h).2, wordMean_mono Γ z hdom n x]

/-- Lemma 5.2's uniform bin estimate on a compact metrizable frame quotient.
The same finite rational sample distribution works for every starting frame and every listed bin. -/
theorem finite_frame_bins [TopologicalSpace.PseudoMetrizableSpace (Cosets Γ)]
    (hμ : ∀ f : Cosets Γ →ᵇ ℝ, (∫ x, operator Γ z f x ∂μ) = ∫ x, f x ∂μ)
    (hdense : Dense (Subgroup.closure ((Γ : Set G) ∪ {z}) : Set G))
    {I : Type*} [Finite I] (B : I → Set (Cosets Γ)) (hB : ∀ i, MeasurableSet (B i))
    (hnull : ∀ i, μ (frontier (B i)) = 0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (i : I) (x : G),
      |wordMean Γ z n x ((B i).indicator (fun _ => 1)) - μ.real (B i)| < ε := by
  rw [Filter.eventually_all]
  intro i
  have hlo := eventually_upper Γ z μ hμ hdense (B i) (hnull i) hε
  have hhi := eventually_upper Γ z μ hμ hdense (B i)ᶜ (by simpa [frontier_compl] using hnull i) hε
  filter_upwards [hlo,hhi] with n lo hi x
  have hv := hi x
  rw [measureReal_compl (hB i), probReal_univ] at hv
  exact abs_lt.mpr ⟨by linarith [wordMean_compl Γ z n x (B i)], by linarith [lo x]⟩

end Hecke

end BorderVNP
end Computability
end OAI

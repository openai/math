import OAI.LinearAlgebra.SpectralBooks.SpineNet
import OAI.LinearAlgebra.SpectralBooks.SpineConditioning
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Tactic.Linarith

/-!
# The Gaussian cost of adjoining tips to the spine ball

The proof of the Student bound conditions on an increasing resolution of the unit
ball in the spine. A tip of height `a` changes the support in the direction
`(g,z)` from `s(g)` to `max (s(g)) (a*z)`.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators

section Convergence

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {ι : Type*} [Fintype ι]

/-- Dominated convergence in the spine-ball inequality. The finite supports
are nonnegative since their sets contain the origin, and bounded by the
support of the whole ball. -/
theorem tendsto_spineConditioning_integral (s : ℕ → Ω → ℝ) (H : Ω → ℝ) (tip : ι → Ω → ℝ)
    (hs : ∀ n, AEStronglyMeasurable (s n) μ) (hH : Integrable H μ)
    (htip : ∀ i, Integrable (tip i) μ)
    (hs0 : ∀ n x, 0 ≤ s n x) (hsH : ∀ n x, s n x ≤ H x)
    (hlim : ∀ x, Tendsto (fun n ↦ s n x) atTop (𝓝 (H x))) :
    Tendsto (fun n ↦ (∫ x, s n x ∂μ) +
        ∑ i, ∫ x, max (tip i x - s n x) 0 ∂μ) atTop
      (𝓝 ((∫ x, H x ∂μ) + ∑ i, ∫ x, max (tip i x - H x) 0 ∂μ)) := by
  apply Tendsto.add
  · apply tendsto_integral_of_dominated_convergence H hs hH
    · exact fun n ↦ ae_of_all μ fun x ↦ by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (hs0 n x)] using hsH n x
    · exact ae_of_all μ hlim
  · apply tendsto_finsetSum
    intro i _
    apply tendsto_integral_of_dominated_convergence (fun x ↦ ‖tip i x‖)
    · exact fun n ↦ ((htip i).aestronglyMeasurable.sub (hs n)).sup aestronglyMeasurable_const
    · exact (htip i).norm
    · refine fun n ↦ ae_of_all μ fun x ↦ ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _), Real.norm_eq_abs]
      exact max_le ((sub_le_self _ (hs0 n x)).trans (le_abs_self _)) (abs_nonneg _)
    · exact ae_of_all μ fun x ↦ (tendsto_const_nhds.sub (hlim x)).max tendsto_const_nhds

/-- Adjoining one point changes the integral of the support by the expected
positive part of the difference. -/
theorem integral_max_sub_integral {s b : Ω → ℝ} (hs : Integrable s μ) (hb : Integrable b μ) :
    (∫ x, max (s x) (b x) ∂μ) - (∫ x, s x ∂μ) = ∫ x, max (b x - s x) 0 ∂μ := by
  have hm : Integrable (fun x ↦ max (s x) (b x)) μ := hs.sup hb
  rw [← integral_sub hm hs]
  apply integral_congr_ae
  exact ae_of_all μ fun x ↦ by
    change max (s x) (b x) - s x = max (b x - s x) 0
    by_cases h : s x ≤ b x
    · rw [max_eq_right h, max_eq_left (sub_nonneg.mpr h)]
    · rw [max_eq_left (le_of_not_ge h), sub_self, max_eq_right (sub_nonpos.mpr (le_of_not_ge h))]

end Convergence

section SpineBall

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {X ι : Type*} [DecidableEq X] [Fintype ι]

/-- The independent Gaussian spine and page-normal coordinates, respectively. -/
noncomputable abbrev spineGaussian (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] :=
  (stdGaussian E).prod (gaussianReal 0 1)

/-- The expression in parentheses on the right side of equation `eq:spine-ball`. -/
noncomputable def spineBallExpectation (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] (a : ι → ℝ) : ℝ :=
  (∫ w : E × ℝ, ‖w.1‖ ∂spineGaussian E) +
  ∑ i, ∫ w : E × ℝ, max (a i * w.2 - ‖w.1‖) 0 ∂spineGaussian E

/-- Equation `eq:spine-ball`, obtained from intersecting submodularity
and the two instances of the finite-set flat diagonal law on each page. -/
theorem diagonal_le_spineBall (δ : Finset X → ℝ) (hmono : Monotone δ)
    (hsub : IntersectingSubmodular δ) (spine : E → X) (tip : ι → X) (a : ι → ℝ)
    (hbase : ∀ B : Finset E, 0 ∈ B → (∀ x ∈ B, ‖x‖ ≤ 1) →
      δ (B.image spine) = Real.sqrt (2 * Real.pi) *
        ∫ w : E × ℝ, spineSupport B w.1 ∂spineGaussian E)
    (hpage : ∀ (i : ι) (B : Finset E), 0 ∈ B → (∀ x ∈ B, ‖x‖ ≤ 1) →
      δ (insert (tip i) (B.image spine)) = Real.sqrt (2 * Real.pi) *
        ∫ w : E × ℝ, max (spineSupport B w.1) (a i * w.2) ∂spineGaussian E) :
    δ (Finset.univ.image tip) ≤ Real.sqrt (2 * Real.pi) * spineBallExpectation E a := by
  obtain ⟨B, hzero, hball, hnet⟩ := exists_spineSupport_net E
  let s (n : ℕ) (w : E × ℝ) := spineSupport (B n) w.1
  have hs (n : ℕ) : AEStronglyMeasurable (s n) (spineGaussian E) :=
    ((continuous_spineSupport (B n)).comp continuous_fst).aestronglyMeasurable
  have hn : Integrable (fun w : E × ℝ ↦ ‖w.1‖) (spineGaussian E) :=
    (IsGaussian.integrable_id (μ := stdGaussian E)).norm.comp_fst _
  have hz (i : ι) : Integrable (fun w : E × ℝ ↦ a i * w.2) (spineGaussian E) :=
    ((IsGaussian.integrable_id (μ := gaussianReal 0 1)).comp_snd _).const_mul (a i)
  have hs0 n (w : E × ℝ) : 0 ≤ s n w := spineSupport_nonneg (B n) w.1
  have hsN n (w : E × ℝ) : s n w ≤ ‖w.1‖ := spineSupport_le_norm (hball n) w.1
  have hsi (n : ℕ) : Integrable (s n) (spineGaussian E) := by
    refine hn.mono' (hs n) (ae_of_all _ fun w ↦ ?_)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hs0 n w)] using hsN n w
  have hlim := tendsto_spineConditioning_integral s (fun w ↦ ‖w.1‖)
    (fun i w ↦ a i * w.2) hs hn hz hs0 hsN (fun w ↦ hnet w.1)
  unfold spineBallExpectation
  apply ge_of_tendsto' (tendsto_const_nhds.mul hlim)
  intro n
  calc
    δ (Finset.univ.image tip)
      ≤ δ ((B n).image spine) +
          ∑ i, (δ (insert (tip i) ((B n).image spine)) - δ ((B n).image spine)) :=
        conditioning_image_le hmono hsub (Finset.Nonempty.image ⟨0, hzero n⟩ _) Finset.univ tip
    _ = _ := by
      simp_rw [hpage _ _ (hzero n) (hball n), hbase _ (hzero n) (hball n), ← mul_sub]
      rw [mul_add, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      exact integral_max_sub_integral (hsi n) (hz i)

omit [BorelSpace E] in
/-- Price comparison for the book tips after substituting the spine-ball
estimate for the diagonal. The premise is the normalized spectral price
bound, multiplied through by the diagonal price. -/
theorem tipPrice_le_spineBall {m a : ι → ℝ} {L D : ℝ} (hL : 0 ≤ L)
    (hprice : ∑ i, a i * m i ≤ L * D)
    (hball : D ≤ Real.sqrt (2 * Real.pi) * spineBallExpectation E a) :
    ∑ i, a i * m i ≤ L * Real.sqrt (2 * Real.pi) * spineBallExpectation E a := by
  simpa only [mul_assoc] using hprice.trans (mul_le_mul_of_nonneg_left hball hL)

end SpineBall

end SpectralBooks
end LinearAlgebra
end OAI

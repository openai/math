import OAI.LinearAlgebra.SpectralBooks.ConvexPatch
import OAI.LinearAlgebra.SpectralBooks.LocalPatch
import OAI.LinearAlgebra.SpectralBooks.SpineConditioning
import Mathlib.Analysis.Convex.Hull

/-! # Passing from interior tangent prices to the price of a Euclidean patch

At a positive dilation, the marginal bound at each occupied site involves its
normal cone. These cones partition the Gaussian directions up to null sets.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology RealInnerProductSpace Classical

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Dilation about the origin preserves the normal cone at the corresponding site. -/
theorem normalConeAtZero_centeredSites_smul (S : Finset E) (v : E) {t : ℝ} (ht : 0 < t) :
    normalConeAtZero (centeredSites (S.image (t • ·)) (t • v)) =
      normalConeAtZero (centeredSites S v) := by
  ext u
  simp [mem_normalConeAtZero_centeredSites, real_inner_smul_right, ht]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

private def marginal (S : Finset E) (v : E) : ℝ :=
  Real.sqrt (2 * Real.pi) * ∫ u in normalConeAtZero (centeredSites S v),
    max ⟪u, v⟫ 0 ∂stdGaussian E

/-- The collective dilation increment is at most the sum of the individual
normal-cone marginals, even when several of the new sites coincide. -/
private theorem eventually_dilation_increment_div_le
    (δ : Finset E → ℝ) (hmono : Monotone δ) (hsub : IntersectingSubmodular δ)
    {S : Finset E} (h0 : 0 ∈ S) (t : ℝ)
    (hlocal : ∀ v ∈ S, ∀ ε > (0 : ℝ), ∀ᶠ h in 𝓝[>] (0 : ℝ),
      (δ (insert (t • v + h • v) (S.image (t • ·))) - δ (S.image (t • ·))) / h ≤
        marginal S v + ε) :
    ∀ ε > (0 : ℝ), ∀ᶠ h in 𝓝[>] (0 : ℝ),
      (δ (S.image ((t + h) • ·)) - δ (S.image (t • ·))) / h ≤ meanWidth S ⟨0, h0⟩ + ε := by
  intro ε hε
  have hS : S.Nonempty := ⟨0, h0⟩
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  filter_upwards [self_mem_nhdsWithin, (eventually_all_finset S).mpr
    (fun v hv ↦ hlocal v hv (ε / S.card) (div_pos hε hcard))]
    with h (hh : 0 < h) hbound
  have hc := conditioning_image_le hmono hsub (hS.image (t • ·)) S ((t + h) • ·)
  calc
    _ ≤ (∑ v ∈ S, (δ (insert ((t + h) • v) (S.image (t • ·))) - δ (S.image (t • ·)))) / h :=
      div_le_div_of_nonneg_right (by linarith only [hc]) hh.le
    _ = ∑ v ∈ S, (δ (insert (t • v + h • v) (S.image (t • ·))) -
        δ (S.image (t • ·))) / h := by rw [Finset.sum_div]; simp_rw [add_smul]
    _ ≤ ∑ v ∈ S, (marginal S v + ε / S.card) := Finset.sum_le_sum hbound
    _ = meanWidth S ⟨0, h0⟩ + ε := by
      rw [Finset.sum_add_distrib, show ∑ v ∈ S, marginal S v = meanWidth S ⟨0, h0⟩ from
        sum_normalCone_marginals h0, Finset.sum_const, nsmul_eq_mul]
      field_simp

/-- The patch reduction of the flat diagonal law. Translate a relative interior
site to the origin and include it in `S`. The tangent hypothesis is used only at
strictly interior dilations of its vertices. The hull condition concerns the
dilated configurations inside the given patch. -/
theorem flatDiagonalLaw_of_tangentMeanWidth
    (δ : Finset E → ℝ) (hmono : Monotone δ) (hsub : IntersectingSubmodular δ)
    {S : Finset E} (h0 : 0 ∈ S) (hzero : δ {0} = 0)
    (hhull : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ T : Finset E,
      (T : Set E) ⊆ convexHull ℝ (S.image (t • ·) : Set E) →
      δ (S.image (t • ·) ∪ T) = δ (S.image (t • ·)))
    (hconv : ConvexOn ℝ (Icc (0 : ℝ) 1) (fun t ↦ δ (S.image (t • ·))))
    (hcont : ContinuousOn (fun t : ℝ ↦ δ (S.image (t • ·))) (Icc 0 1))
    (htan : ∀ t ∈ Ico (0 : ℝ) 1, ∀ v ∈ S, HasTangentMeanWidth δ (t • v)) :
    δ S = meanWidth S ⟨0, h0⟩ := by
  have hS : S.Nonempty := ⟨0, h0⟩
  have htan₀ : HasTangentMeanWidth δ 0 := by simpa using htan 0 ⟨le_rfl, zero_lt_one⟩ 0 h0
  have h := convexPatch_price_eq_of_eventually_increment_le hconv hcont
    (by simpa [Finset.image_const hS] using hzero) (by simpa using htan₀ S hS) ?_
  · simpa using h
  · intro t ht
    apply eventually_dilation_increment_div_le δ hmono hsub h0 t
    intro v hv ε hε
    have hy := Finset.mem_image_of_mem (t • ·) hv
    have hlocal := eventually_price_increment_div_le_normalCone δ
      (fun _ _ _ h ↦ hmono h) hsub (hhull t ht) hy v
      (htan t ⟨ht.1.le, ht.2⟩ v hv) hε
    simpa only [marginal, normalConeAtZero_centeredSites_smul S v ht.1] using hlocal

end

end

end SpectralBooks
end LinearAlgebra
end OAI

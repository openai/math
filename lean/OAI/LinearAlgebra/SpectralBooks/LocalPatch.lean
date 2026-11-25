import OAI.LinearAlgebra.SpectralBooks.PatchIncrement
import OAI.LinearAlgebra.SpectralBooks.WidthPartition

/-!
# Local comparison at a site of a convex Euclidean patch

To estimate the increment when a new site separates from an old one, shrink
the configuration about the old site. The contracted points lie in its convex
hull. On dividing by the step size, the prices of the contracted configurations
converge to the tangent mean widths. Taking the dilation to infinity isolates
the directions that support the original site.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped Topology RealInnerProductSpace Classical

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Normalized prices of translated and contracted finite configurations have
the specified Gaussian mean width as their tangent price at `y`. -/
def HasTangentMeanWidth (δ : Finset E → ℝ) (y : E) : Prop :=
  ∀ (U : Finset E) (hU : U.Nonempty),
    Tendsto (fun h : ℝ ↦ δ (U.image (fun w ↦ y + h • w)) / h)
      (𝓝[>] 0) (𝓝 (meanWidth U hU))

variable (δ : Finset E → ℝ)
  (hmono : ∀ ⦃S T : Finset E⦄, S.Nonempty → S ⊆ T → δ S ≤ δ T)
  (hsub : IntersectingSubmodular δ)
  {S : Finset E}
  (hhull : ∀ T : Finset E, (T : Set E) ⊆ convexHull ℝ (S : Set E) →
    δ (S ∪ T) = δ S)

include hmono hsub hhull

omit [BorelSpace E] in
/-- At a fixed dilation `M`, the price increment at a site is bounded to
first order by the width increment of the centered dilate. -/
theorem eventually_price_increment_div_le_dilated {y : E} (hy : y ∈ S) (v : E)
    (htangent : HasTangentMeanWidth δ y) {M : ℝ} (hM : 0 < M) {ε : ℝ} (hε : 0 < ε) :
    let U := (centeredSites S y).image (M • ·)
    ∀ᶠ h in 𝓝[>] (0 : ℝ), (δ (insert (y + h • v) S) - δ S) / h ≤
      meanWidth (insert v U) (Finset.insert_nonempty _ _) -
      meanWidth U ((Finset.Nonempty.image (⟨y, hy⟩ : S.Nonempty) _).image _) + ε := by
  let U := (centeredSites S y).image (M • ·)
  have hU : U.Nonempty := (Finset.Nonempty.image (⟨y, hy⟩ : S.Nonempty) _).image _
  have hlim := (htangent (insert v U) (Finset.insert_nonempty _ _)).sub (htangent U hU)
  have happ := hlim.eventually_lt_const (lt_add_of_pos_right _ hε)
  filter_upwards [Ioo_mem_nhdsGT (one_div_pos.mpr hM), happ] with h hh hbound
  let P := U.image (fun w ↦ y + h • w)
  have hPS : (P : Set E) ⊆ convexHull ℝ (S : Set E) := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨w, hw, rfl⟩
    rcases Finset.mem_image.mp hw with ⟨z, hz, rfl⟩
    rcases Finset.mem_image.mp hz with ⟨a, ha, rfl⟩
    rw [smul_smul]
    apply segment_subset_convexHull (s := (S : Set E)) hy ha
    rw [segment_eq_image']
    exact Set.mem_image_of_mem _ ⟨mul_nonneg hh.1.le hM.le, ((lt_div_iff₀ hM).mp hh.2).le⟩
  have hinc := price_increment_le_of_hull_patch δ hmono hsub hhull (hU.image _) hPS
    (y + h • v)
  simp only [Finset.image_insert, ← sub_div] at hbound
  exact (div_le_div_of_nonneg_right hinc hh.1.le).trans hbound.le

/-- Upper right marginal price at a site in terms of the positive part of the
motion projected onto directions supporting that site. -/
theorem eventually_price_increment_div_le_normalCone {y : E} (hy : y ∈ S)
    (v : E) (htangent : HasTangentMeanWidth δ y) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ), (δ (insert (y + h • v) S) - δ S) / h ≤
      Real.sqrt (2 * Real.pi) *
        (∫ u in normalConeAtZero (centeredSites S y), max ⟪u, v⟫ 0 ∂stdGaussian E) + ε := by
  have h0 : 0 ∈ centeredSites S y := Finset.mem_image.mpr ⟨y, hy, sub_self y⟩
  have hlim := tendsto_meanWidth_insert_smul_sub h0 v
  have happ := hlim.eventually_lt_const (lt_add_of_pos_right _ (half_pos hε))
  obtain ⟨M, hM, hnear⟩ := ((eventually_gt_atTop (0 : ℝ)).and happ).exists
  filter_upwards [eventually_price_increment_div_le_dilated δ hmono hsub hhull hy v htangent
    hM (half_pos hε)] with h hbound
  linarith

end

end

end SpectralBooks
end LinearAlgebra
end OAI

import OAI.LinearAlgebra.SpectralBooks.Book
import OAI.LinearAlgebra.SpectralBooks.FacetChart

/-! # Distances across the two outward slabs

The reflected path gives an upper bound from the two page metrics. The
squared-distance support inequality on the other page makes it an equality.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Set
open scoped RealInnerProductSpace

variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [PseudoMetricSpace X]

private theorem dist_normal_translate {p q e : E} {r : ℝ} (he : ‖e‖ = 1)
    (hperp : ⟪p, e⟫ = ⟪q, e⟫) :
    dist (p + r • e) q ^ 2 = dist p q ^ 2 + r ^ 2 := by
  simp only [dist_eq_norm, show p + r • e - q = (p - q) + r • e by abel,
    norm_add_sq_real, real_inner_smul_right, inner_sub_left, hperp, sub_self, mul_zero, add_zero,
    norm_smul, Real.norm_eq_abs, he, mul_one, sq_abs]

/-- If the two charts are isometric over the facet and the squared-distance
support inequality holds at the foot of the first tip, then the cross distance
is exactly the reflected Euclidean distance. -/
theorem chart_sq_cross_distance {F C : Set E} {p q e : E} {r s : ℝ} (he : ‖e‖ = 1)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hF : Convex ℝ F) (hp : p ∈ F) (hq : q ∈ F)
    (hplane : ∀ z ∈ F, ⟪z, e⟫ = ⟪p, e⟫)
    (hFC : F ⊆ C) (hx : p + r • e ∈ C) (hy : q + s • e ∈ C)
    {b c : E → X} (hb : ∀ x ∈ C, ∀ y ∈ C, dist (b x) (b y) = dist x y)
    (hc : ∀ x ∈ C, ∀ y ∈ C, dist (c x) (c y) = dist x y)
    (hbc : F.EqOn b c)
    (hlower : r ^ 2 + 2 * r * ⟪e, (q + s • e) - p⟫ + ‖(q + s • e) - p‖ ^ 2 ≤
      dist (c (q + s • e)) (b (p + r • e)) ^ 2) :
    dist (b (p + r • e)) (c (q + s • e)) ^ 2 = dist p q ^ 2 + (r + s) ^ 2 := by
  have hseg := hF.segment_subset hp hq
  have hbz (z) (hz : z ∈ segment ℝ p q) :
      dist (b (p + r • e)) (c z) = Real.sqrt (dist p z ^ 2 + r ^ 2) := by
    rw [← hbc (hseg hz), hb _ hx _ (hFC (hseg hz)), ← dist_normal_translate he (hplane z (hseg hz)).symm,
      Real.sqrt_sq dist_nonneg]
  have hcz (z) (hz : z ∈ segment ℝ p q) :
      dist (c z) (c (q + s • e)) = Real.sqrt (dist z q ^ 2 + s ^ 2) := by
    rw [dist_comm (c z), hc _ hy _ (hFC (hseg hz)), dist_comm z q,
      ← dist_normal_translate he ((hplane q hq).trans (hplane z (hseg hz)).symm),
      Real.sqrt_sq dist_nonneg]
  have hu := dist_le_reflected_path hr hs c hbz hcz
  have hU := (Real.le_sqrt dist_nonneg (by positivity)).mp hu
  have hi : ⟪e, (q + s • e) - p⟫ = s := by
    rw [real_inner_comm, inner_sub_left, inner_add_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq, he, hplane q hq]
    ring
  have hd : ‖(q + s • e) - p‖ ^ 2 = dist p q ^ 2 + s ^ 2 := by
    rw [← dist_eq_norm, dist_comm p q]
    exact dist_normal_translate he (hplane q hq)
  rw [hi, hd, dist_comm (c _)] at hlower
  linarith only [hU, hlower, show (r + s) ^ 2 = r ^ 2 + 2 * r * s + s ^ 2 by ring]

open Book MeasureTheory

/-- Exact cross distances of the outward slabs in the doubled coordinate cubes,
from the outward-increment integral at the relative interior feet. -/
theorem doubled_cube_cross_distance {ι X : Type*} [Fintype ι] [DecidableEq ι] [MetricSpace X]
    [MeasurableSpace (LiftSphere (EuclideanSpace ℝ ι))] [BorelSpace (LiftSphere (EuclideanSpace ℝ ι))]
    (σ : Measure (LiftSphere (EuclideanSpace ℝ ι))) [IsFiniteMeasure σ] [σ.IsOpenPosMeasure]
    (hX : SharpIntegralFillings.IsCAT0 X) {b c : EuclideanSpace ℝ ι → X} {i : ι}
    (hb : ∀ u ∈ coordinateCube ι 2, ∀ v ∈ coordinateCube ι 2, dist (b u) (b v) = dist u v)
    (hc : ∀ u ∈ coordinateCube ι 2, ∀ v ∈ coordinateCube ι 2, dist (c u) (c v) = dist u v)
    (hbc : (coordinateCube ι 1).EqOn b c)
    (hcmp : ∀ p ∈ upperUnitCubeFacet i, (∀ j, j ≠ i → p j ∈ Ioo (-1 : ℝ) 1) →
      ∀ r ∈ Ioc (0 : ℝ) 1, FacetOutwardComparison σ i
        (fun w ↦ dist (c w) (b (p + r • EuclideanSpace.single i 1))))
    {p q : EuclideanSpace ℝ ι} (hp : p ∈ upperUnitCubeFacet i) (hq : q ∈ upperUnitCubeFacet i)
    {r s : ℝ} (hr : r ∈ Icc 0 1) (hs : s ∈ Icc 0 1) :
    dist (b (p + r • EuclideanSpace.single i 1)) (c (q + s • EuclideanSpace.single i 1)) ^ 2 =
      dist p q ^ 2 + (r + s) ^ 2 := by
  have hF : Convex ℝ (upperUnitCubeFacet i) := by
    intro u hu v hv a a₁ ha ha₁ hsum
    refine ⟨(convex_coordinateCube (ι := ι) (zero_le_one : (0 : ℝ) ≤ 1)) hu.1 hv.1 ha ha₁ hsum,
      ?_⟩
    simpa [PiLp.add_apply, PiLp.smul_apply, hu.2, hv.2] using hsum
  have hsub : upperUnitCubeFacet i ⊆ coordinateCube ι 2 := fun _ hz ↦
    interior_subset (coordinateCube_one_subset_interior_two hz.1)
  apply chart_sq_cross_distance (by simp) hr.1 hs.1 hF hp hq _ hsub
    (outward_tip_mem_coordinateCube_two hp hr) (outward_tip_mem_coordinateCube_two hq hs) hb hc
    (fun _ hz ↦ hbc hz.1)
  · exact chart_sq_cross_distance_lower_bound σ hX hb hc hbc hcmp hp hr
      (outward_tip_mem_coordinateCube_two hq hs)
  · intro z hz
    simp [EuclideanSpace.inner_single_right, hz.2, hp.2]

end SpectralBooks
end LinearAlgebra
end OAI

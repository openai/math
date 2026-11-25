import OAI.LinearAlgebra.SpectralBooks.BookCAT0
import OAI.LinearAlgebra.SpectralBooks.FacetIntegral

/-! # Cross distances in the doubled Euclidean cubes

The normal-cone comparison is needed only at interior differentiability
points above the facet, for feet in the relative interior and positive
heights. The lower bound then extends to the entire closed slab.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open SharpIntegralFillings Book MeasureTheory Filter Set
open scoped InnerProductSpace Topology

section

variable {ι X : Type*} [Fintype ι] [DecidableEq ι] [MetricSpace X]
variable [MeasurableSpace (LiftSphere (EuclideanSpace ℝ ι))] [BorelSpace (LiftSphere (EuclideanSpace ℝ ι))]

/-- The sphere integral comparison of the outward-increment argument, stated
in the coordinates of the doubled cube. Here `f` measures the distance to a
fixed point on the other page. -/
def FacetOutwardComparison (σ : Measure (LiftSphere (EuclideanSpace ℝ ι))) (i : ι) (f : (EuclideanSpace ℝ ι) → ℝ) : Prop :=
  ∀ y ∈ interior (coordinateCube ι 2), 1 < y i → 0 < f y → DifferentiableAt ℝ f y →
    ∫ n in normalCone (coordinateCube ι 1) y, outwardWeight (EuclideanSpace.single i 1) n ∂σ ≤
    ∫ n in normalCone (coordinateCube ι 1) y ∩
      {n | ⟪(n : Lift (EuclideanSpace ℝ ι)), liftedDirection (gradient f y) (f y)⟫_ℝ ≤ 0},
      outwardWeight (EuclideanSpace.single i 1) n ∂σ

variable (σ : Measure (LiftSphere (EuclideanSpace ℝ ι))) [IsFiniteMeasure σ] [σ.IsOpenPosMeasure]
    {b c : (EuclideanSpace ℝ ι) → X} {i : ι}

private theorem chart_lower_at_interior_foot (hX : IsCAT0 X)
    (hb : ∀ u ∈ coordinateCube ι 2, ∀ v ∈ coordinateCube ι 2, dist (b u) (b v) = dist u v)
    (hc : ∀ u ∈ coordinateCube ι 2, ∀ v ∈ coordinateCube ι 2, dist (c u) (c v) = dist u v)
    (hbc : (coordinateCube ι 1).EqOn b c) {p : (EuclideanSpace ℝ ι)} (hp : p ∈ upperUnitCubeFacet i)
    (hint : ∀ j, j ≠ i → p j ∈ Ioo (-1 : ℝ) 1) {r : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1)
    (hcmp : FacetOutwardComparison σ i (fun w ↦ dist (c w) (b (p + r • EuclideanSpace.single i 1))))
    {z : (EuclideanSpace ℝ ι)} (hz : z ∈ coordinateCube ι 2) :
    r ^ 2 + 2 * r * ⟪EuclideanSpace.single i 1, z - p⟫_ℝ + ‖z - p‖ ^ 2 ≤
      dist (c z) (b (p + r • EuclideanSpace.single i 1)) ^ 2 := by
  let e := EuclideanSpace.single i (1 : ℝ)
  let x := b (p + r • e)
  have hip : p ∈ interior (coordinateCube ι 2) := coordinateCube_one_subset_interior_two hp.1
  have hsub : coordinateCube ι 1 ⊆ coordinateCube ι 2 :=
    coordinateCube_one_subset_interior_two.trans interior_subset
  have ht := outward_tip_mem_coordinateCube_two hp (r := r) ⟨hr.le, hr₁⟩
  have he : ‖e‖ = 1 := by simp [e]
  have hface (w : (EuclideanSpace ℝ ι)) (hw : w ∈ upperUnitCubeFacet i) :
      dist (c w) x = ‖w - (p + r • e)‖ := by
    rw [← hbc hw.1, show x = b (p + r • e) from rfl, hb _ (hsub hw.1) _ ht, dist_eq_norm]
  have hfp : dist (c p) x = r := by
    rw [hface p hp, sub_add_eq_sub_sub, sub_self, zero_sub, norm_neg, norm_smul, he,
      Real.norm_eq_abs, abs_of_pos hr, mul_one]
  have hcv := convex_coordinateCube (ι := ι) (by norm_num : 0 ≤ (2 : ℝ))
  apply facet_sq_distance_of_outward_integral σ (patch_lipschitzOn_dist hc x)
    (cat0_patch_convexOn_dist hX hcv hc x) (cat0_patch_strongConvexOn_dist_sq hX hcv hc x)
    hip hr hfp he (isCompact_coordinateCube 1) _ _ (eventually_tangent_line_facet_distance
      hsub hp.2 hint hface) hz
  · intro w hw
    simpa [e, EuclideanSpace.inner_single_left, PiLp.sub_apply, hp.2] using
      sub_nonpos.mpr (hw i).2
  · intro y hy hout hpos hd
    apply hcmp y hy _ hpos hd
    simpa [e, EuclideanSpace.inner_single_right, PiLp.sub_apply, hp.2] using hout

/-- Equation (book-cross-distance) for two doubled charts in a CAT(0) space
agreeing on the inner cube. The comparison of normal-cone integrals is required
only for positive heights and relative interior feet. -/
theorem chart_sq_cross_distance_lower_bound (hX : IsCAT0 X)
    (hb : ∀ u ∈ coordinateCube ι 2, ∀ v ∈ coordinateCube ι 2, dist (b u) (b v) = dist u v)
    (hc : ∀ u ∈ coordinateCube ι 2, ∀ v ∈ coordinateCube ι 2, dist (c u) (c v) = dist u v)
    (hbc : (coordinateCube ι 1).EqOn b c)
    (hcmp : ∀ p ∈ upperUnitCubeFacet i, (∀ j, j ≠ i → p j ∈ Ioo (-1 : ℝ) 1) →
      ∀ r ∈ Ioc (0 : ℝ) 1, FacetOutwardComparison σ i
        (fun w ↦ dist (c w) (b (p + r • EuclideanSpace.single i 1))))
    {p : (EuclideanSpace ℝ ι)} (hp : p ∈ upperUnitCubeFacet i) {r : ℝ} (hr : r ∈ Icc 0 1)
    {z : (EuclideanSpace ℝ ι)} (hz : z ∈ coordinateCube ι 2) :
    r ^ 2 + 2 * r * ⟪EuclideanSpace.single i 1, z - p⟫_ℝ + ‖z - p‖ ^ 2 ≤
      dist (c z) (b (p + r • EuclideanSpace.single i 1)) ^ 2 := by
  rcases hr.1.eq_or_lt with hzero | hpos
  · subst r
    simp [hbc hp.1, hc _ hz _ (interior_subset (coordinateCube_one_subset_interior_two hp.1)),
      dist_eq_norm]
  let e := EuclideanSpace.single i (1 : ℝ)
  obtain ⟨u, hu, hui⟩ := exists_seq_in_facet_relative_interior hp
  have hbLip : LipschitzOnWith 1 b (coordinateCube ι 2) :=
    lipschitzOnWith_iff_dist_le_mul.mpr (fun _ hx _ hy ↦ by simp [hb _ hx _ hy])
  have htip : Tendsto (fun n ↦ b (u n + r • e)) atTop (𝓝 (b (p + r • e))) := by
    apply (hbLip.continuousOn _ (outward_tip_mem_coordinateCube_two hp hr)).tendsto.comp
    exact tendsto_nhdsWithin_iff.mpr ⟨hu.add tendsto_const_nhds, Eventually.of_forall
      (fun n ↦ outward_tip_mem_coordinateCube_two (hui n).1 hr)⟩
  have hzsub : Tendsto (fun n ↦ z - u n) atTop (𝓝 (z - p)) := tendsto_const_nhds.sub hu
  exact le_of_tendsto_of_tendsto' ((tendsto_const_nhds.add
    (tendsto_const_nhds.mul (tendsto_const_nhds.inner hzsub))).add (hzsub.norm.pow 2))
    ((tendsto_const_nhds.dist htip).pow 2)
    (fun n ↦ chart_lower_at_interior_foot σ hX hb hc hbc (hui n).1 (hui n).2 hpos hr.2
      (hcmp _ (hui n).1 (hui n).2 _ ⟨hpos, hr.2⟩) hz)

end

end SpectralBooks
end LinearAlgebra
end OAI

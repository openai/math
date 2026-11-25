import OAI.Geometry.HyperbolicGroups.MetricProduct
import OAI.LinearAlgebra.SpectralBooks.CubeGrid
import OAI.LinearAlgebra.SpectralBooks.BookComparison

/-! # The two doubled cubes in the pointed metric ultralimit

The input to this construction is the pair of finite grids after private wire
prices have doubled. Grid points are indexed in doubled coordinates in `[-2,2]^ι`,
so their distances within each grid are the ordinary Euclidean distances of the
indices. Every inner corner comes with a common auxiliary site whose distances
to the center and the two copies of the corresponding outer corner are bounded.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Filter Set HyperbolicObstruction SharpIntegralFillings
open scoped Topology

section

variable {ι : Type*} [Fintype ι] {X : ℕ → Type*} [∀ n, MetricSpace (X n)]

/-- Metric data from the finite configurations produced by doubling on successively finer grids. -/
structure DoubledGridFamily (ι : Type*) [Fintype ι] {X : ℕ → Type*}
    [∀ n, MetricSpace (X n)] (o : ∀ n, X n) where
  site : ∀ n, Bool → (cubeGrid ι n) → X n
  center : ∀ n k, site n k ⟨0, zero_mem_cubeGrid ι n⟩ = o n
  wire : ∀ n k x y, dist (site n k x) (site n k y) = dist (x : EuclideanSpace ℝ ι) y
  auxiliary : ∀ n z (hz : z ∈ coordinateCubeCorners ι 1), ∃ p : X n,
    dist (o n) p ≤ ‖z‖ ∧ ∀ k, dist (site n k ⟨(2 : ℝ) • z, double_corner_mem_cubeGrid n hz⟩) p ≤ ‖z‖

namespace DoubledGridFamily

variable {o : ∀ n, X n} (G : DoubledGridFamily ι o) (U : Ultrafilter ℕ)

/-- The bounded sequence of approximating points for a fixed point of either chart. -/
noncomputable def gridSection (k : Bool) (x : EuclideanSpace ℝ ι) : MetricLimit.Bounded U X o where
  val n := G.site n k ⟨_, gridPoint_mem n x⟩
  bound := by
    obtain ⟨R, hR⟩ := (isCompact_coordinateCube (ι := ι) 2).isBounded.subset_closedBall 0
    refine ⟨R, fun n ↦ ?_⟩
    rw [← G.center n k, G.wire, dist_comm]
    exact hR (cubeGrid_subset ι n (gridPoint_mem n x))

private theorem gridSection_at_grid {n : ℕ} (k : Bool) {x : EuclideanSpace ℝ ι}
    (hx : x ∈ cubeGrid ι n) : (G.gridSection U k x).val n = G.site n k ⟨x, hx⟩ :=
  congrArg (G.site n k) (Subtype.ext (gridPoint_eq_of_mem hx))

/-- Each chart of the doubled cube in the same pointed metric ultralimit. -/
noncomputable def chart (k : Bool) (x : EuclideanSpace ℝ ι) :
    MetricLimit.Space (U := U) (X := X) (o := o) := MetricLimit.point (G.gridSection U k x)

/-- The whole doubled cube appears isometrically, by convergence of the grid coordinates. -/
theorem chart_dist (hU : (U : Filter ℕ) ≤ atTop) (k : Bool)
    {x y : EuclideanSpace ℝ ι} (hx : x ∈ coordinateCube ι 2) (hy : y ∈ coordinateCube ι 2) :
    dist (G.chart U k x) (G.chart U k y) = dist x y := by
  apply tendsto_nhds_unique (MetricLimit.tendsto_point_dist (G.gridSection U k x) (G.gridSection U k y))
  exact (((tendsto_gridPoint hx).dist (tendsto_gridPoint hy)).mono_left hU).congr
    (fun n ↦ (G.wire n k ⟨_, gridPoint_mem n x⟩ ⟨_, gridPoint_mem n y⟩).symm)

/-- The two ultralimit charts of the doubled cube agree at every point of the inner cube. -/
theorem charts_agree (hU : (U : Filter ℕ) ≤ atTop) (hX : ∀ n, CATZero (X n)) :
    (coordinateCube ι 1).EqOn (G.chart U false) (G.chart U true) := by
  have hcat := isCAT0_of_catZero (MetricLimit.catZero (U := U) (o := o) hX)
  apply cat0_doubled_charts_agree_of_auxiliaries hcat
    (fun _ hx _ hy ↦ G.chart_dist U hU false hx hy) (fun _ hx _ hy ↦ G.chart_dist U hU true hx hy)
  · apply congrArg MetricLimit.point
    ext n
    rw [G.gridSection_at_grid U false (zero_mem_cubeGrid ι n),
      G.gridSection_at_grid U true (zero_mem_cubeGrid ι n), G.center, G.center]
  · intro z hz
    choose p hp htip using fun n ↦ G.auxiliary n z hz
    let aux : MetricLimit.Bounded U X o := ⟨p, ‖z‖, hp⟩
    refine ⟨MetricLimit.point aux, ?_, ?_⟩
    · apply le_of_tendsto' (MetricLimit.tendsto_point_dist (G.gridSection U false 0) aux)
      intro n
      rw [G.gridSection_at_grid U false (zero_mem_cubeGrid ι n), G.center]
      exact hp n
    · have h (k : Bool) : dist (G.chart U k ((2 : ℝ) • z)) (MetricLimit.point aux) ≤ ‖z‖ := by
        apply le_of_tendsto' (MetricLimit.tendsto_point_dist (G.gridSection U k _) aux)
        intro n
        rw [G.gridSection_at_grid U k (double_corner_mem_cubeGrid n hz)]
        exact htip n k
      exact ⟨h false, h true⟩

end DoubledGridFamily
end

end SpectralBooks
end LinearAlgebra
end OAI

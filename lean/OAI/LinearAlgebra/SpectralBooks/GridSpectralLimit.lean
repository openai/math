import OAI.LinearAlgebra.SpectralBooks.GridTensorDoubling
import OAI.LinearAlgebra.SpectralBooks.SpectralGridLimit
import OAI.LinearAlgebra.SpectralBooks.SpectralBookOutward

/-! # The two doubled cubes with their spectral prices

The placements selected on the finite grids induce two isometric cube charts
in the pointed ultralimit, with mean-width prices on each chart and price
three times the inner cube width on their combined outer corners.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section

open Filter Set HyperbolicObstruction
open scoped Topology Classical

section

variable {F ι Y : Type} [Field F] [Fintype ι] [MetricSpace Y]

/-- The two cube charts used in the slab comparison, with the canonical
binary diagonal of the ambient spectral space. -/
structure SpectralCubeCharts (ι : Type) [Fintype ι] (P : SpectralPlacementPrices F Y) where
  chart : Bool → EuclideanSpace ℝ ι → Y
  dist_eq : ∀ k, ∀ x ∈ coordinateCube ι 2, ∀ y ∈ coordinateCube ι 2,
    dist (chart k x) (chart k y) = dist x y
  agree : (coordinateCube ι 1).EqOn (chart false) (chart true)
  width : ∀ k (S : Finset (EuclideanSpace ℝ ι)) (hS : S.Nonempty),
    (S : Set _) ⊆ coordinateCube ι 2 → P.diagonal (S.image (chart k)) = meanWidth S hS
  corner_union : P.diagonal ((coordinateCubeCorners ι 2).image (chart false) ∪
    (coordinateCubeCorners ι 2).image (chart true)) = 3 * innerCubeWidth ι

namespace SpectralCubeCharts

variable {P : SpectralPlacementPrices F Y} (C : SpectralCubeCharts ι P)

/-- The diagonal independence equation in the actual ambient spectral space. -/
theorem independence (L N : Finset (EuclideanSpace ℝ ι))
    (hL : (L : Set _) ⊆ coordinateCube ι 2) (hN : (N : Set _) ⊆ coordinateCube ι 2) :
    let K := (coordinateCubeCorners ι 1).image (C.chart false)
    P.diagonal (K ∪ L.image (C.chart false) ∪ N.image (C.chart true)) =
      P.diagonal (K ∪ L.image (C.chart false)) + P.diagonal (K ∪ N.image (C.chart true)) -
      P.diagonal K :=
  doubled_cube_diagonal_independence P.intersectingSubmodular (fun _ _ _ h ↦ P.diagonal_mono h)
    _ _ C.agree (C.width false) (C.width true) C.corner_union L N hL hN

end SpectralCubeCharts

variable {X : ℕ → Type} [∀ n, MetricSpace (X n)]

/-- Joint convexity of the binary-diagonal tensor passes to the full spectral
structure of the pointed metric ultralimit. -/
theorem SpectralPlacementPrices.metricLimit_jointlyConvexDiagonal
    (U : Ultrafilter ℕ) (Q : ∀ n, SpectralPlacementPrices F (X n)) {o : ∀ n, X n}
    (hX : ∀ n, CATZero (X n)) (hQ : ∀ n, (Q n).JointlyConvexDiagonal (hX n)) :
    (metricLimit (o := o) U Q).JointlyConvexDiagonal (MetricLimit.catZero hX) := by
  intro I _ _ p q t ht
  let D := SiteTensor.Raw.diagonal I F (Fin 2)
  have eq (v : I → MetricLimit.Space (U := U) (o := o)) :
      (metricLimit U Q).price D v = metricLimitPrice (fun n ↦ (Q n).price D) v := by
    choose r hr using fun i ↦ SeparationQuotient.surjective_mk (v i)
    have he : MetricLimit.point ∘ r = v := funext hr
    rw [← he]
    exact tendsto_nhds_unique (metricLimit_price_tendsto U Q D r)
      (tendsto_metricLimitPrice _ _ (fun n ↦ (Q n).collapsed D) (fun n ↦ (Q n).transport D) r)
  change (metricLimit U Q).price D _ ≤ (1 - t) * (metricLimit U Q).price D p +
    t * (metricLimit U Q).price D q
  simpa only [eq] using! (metricLimitPrice_jointConvex hX _ (fun n ↦ (Q n).price D)
    (fun n ↦ (Q n).collapsed D) (fun n ↦ (Q n).transport D) (fun n ↦ hQ n) p q ht)

namespace RealizedGridDoubling

variable {H : SpectralPlacementPrices F (EuclideanSpace ℝ ι)} {Q : ∀ n, SpectralPlacementPrices F (X n)}

/-- The realized finite doubling yields the two cube charts inside the
spectral ultralimit of the very same finite configurations. -/
def spectralCubeCharts (G : RealizedGridDoubling H Q)
    (hflat : ∀ (S : Finset (EuclideanSpace ℝ ι)) (hS : S.Nonempty), H.diagonal S = meanWidth S hS)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hX : ∀ n, CATZero (X n)) :
    SpectralCubeCharts ι (SpectralPlacementPrices.metricLimit (o := fun n ↦ G.place n gridCenter) U Q) := by
  let P := G.gridPrices hflat (fun n _ _ _ h ↦ (Q n).diagonal_mono h) (fun n ↦ (Q n).intersectingSubmodular)
  exact {
    chart := P.family.chart U
    dist_eq := fun k _ hx _ hy ↦ P.family.chart_dist U hU k hx hy
    agree := P.family.charts_agree U hU hX
    width := fun k S hS hc ↦ (SpectralPlacementPrices.metricLimit_diagonal U Q _).trans
      (P.chart_width hU k S hS hc)
    corner_union := (SpectralPlacementPrices.metricLimit_diagonal U Q _).trans
      (P.chart_corner_union_price U) }

end RealizedGridDoubling
end

end

end SpectralBooks
end LinearAlgebra
end OAI

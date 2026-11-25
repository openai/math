import OAI.LinearAlgebra.SpectralBooks.Book.BookOutward
import OAI.LinearAlgebra.SpectralBooks.SpectralFlatLaw

/-!
# Outward comparison for spectral placement prices

We specialize the two-cube calculation to actual prices in a field. The
geometric price input of Proposition `prop:plane` is joint convexity.
The flat law for the charts and the tangent hulls follows from it.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
section

open HyperbolicObstruction Filter Set Book
open scoped Topology Classical

variable {K X ι : Type} [Field K] [MetricSpace X] [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ι

set_option maxHeartbeats 500000 in
/-- The outward comparison in the proof of the book theorem, for a spectral
space over any field. The outer corners have the price supplied by doubling. -/
theorem spectral_facetOutwardComparison
    (P : SpectralPlacementPrices K X) (hX : CATZero X) (hjoint : P.JointlyConvexDiagonal hX)
    (b c : E → X) (i : ι) (v₀ : LiftSphere E)
    (hb : ∀ u ∈ coordinateCube ι 2, ∀ v ∈ coordinateCube ι 2, dist (b u) (b v) = dist u v)
    (hc : ∀ u ∈ coordinateCube ι 2, ∀ v ∈ coordinateCube ι 2, dist (c u) (c v) = dist u v)
    (hbc : (coordinateCube ι 1).EqOn b c)
    (hboth : P.diagonal ((coordinateCubeCorners ι 2).image b ∪ (coordinateCubeCorners ι 2).image c) =
      3 * innerCubeWidth ι)
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (s : ℕ → ℝ) (hs : ∀ n, 0 < s n) (h₀ : Tendsto s atTop (𝓝 0))
    {z : E} (hz : z ∈ coordinateCube ι 2) :
    FacetOutwardComparison (widthSphereMeasure v₀) i (fun w => dist (c w) (b z)) := by
  let C := coordinateCube ι 2
  have hC : Convex ℝ C := convex_coordinateCube (by norm_num)
  have flat (e : E → X) (he : ∀ u ∈ C, ∀ v ∈ C, dist (e u) (e v) = dist u v) :
      ∀ (T : Finset E) (hT : T.Nonempty), (T : Set E) ⊆ C →
        P.diagonal (T.image e) = meanWidth T hT := by
    exact P.flatDiagonalLaw_chart hX hjoint hC he
  apply facetOutwardComparison_of_doubled_cube_prices P.diagonal hX b c i v₀ P.intersectingSubmodular
    (fun _ _ _ h => P.diagonal_mono h) P.diagonal_pair (fun _ => P.diagonal_transport)
    hc hbc (flat b hb) (flat c hc) hboth ω hω s hs h₀ _ hz
  intro y _ _ a H F hF T hT
  exact blowupDiagonal_flatApexHull P hX hjoint ω hs (c y) a H F hF T hT

end

end

end SpectralBooks
end LinearAlgebra
end OAI

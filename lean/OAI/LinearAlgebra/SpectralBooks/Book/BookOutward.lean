import OAI.LinearAlgebra.SpectralBooks.BookCornerIncrement
import OAI.LinearAlgebra.SpectralBooks.Book.BookFacetPrice
import OAI.LinearAlgebra.SpectralBooks.Book.BookTangentMarginal

/-! # The outward sphere comparison from the doubled cubes

The equalities on the corner diagonals give independence. The tangent
construction and the flat law on its Euclidean hull compute the contracted
price limits required for the opposite-page distance function.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
namespace Book

open HyperbolicObstruction Filter Set
open scoped Topology Classical

/-- The flat diagonal law for finite placements on the Euclidean hull of the
tangent flat and the opposite-page apex. -/
def TangentHullWidth (V X : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace (Lift V)] [MetricSpace X]
    (δ : Finset X → ℝ) (ω : Ultrafilter ℕ) {s : ℕ → ℝ} (hs : ∀ n, 0 < s n) (p : X) : Prop :=
  ∀ (a : V) (H : ℝ) (F : flatApexHull a H → Blowup ω hs p), Isometry F →
    ∀ (T : Finset (flatApexHull a H)) (hT : T.Nonempty),
      blowupDiagonal ω hs p δ (T.image F) = meanWidth (T.image Subtype.val) (hT.image _)

variable {ι X : Type*} [Fintype ι] [DecidableEq ι] [MetricSpace X]
local notation "E" => EuclideanSpace ℝ ι

set_option maxHeartbeats 600000 in
/-- The outward comparison for an opposite point of a doubled chart.
The flat diagonal law is used on the two original cubes and on the isometric
Euclidean apex hulls at points of the second cube. -/
theorem facetOutwardComparison_of_doubled_cube_prices
    (δ : Finset X → ℝ) (hX : CATZero X) (b c : E → X) (i : ι) (v₀ : LiftSphere E)
    (hsub : IntersectingSubmodular δ)
    (hmono : ∀ ⦃S T⦄, S.Nonempty → S ⊆ T → δ S ≤ δ T)
    (hpair : ∀ u v : X, δ {u, v} = dist u v) (hmove : DiagonalTransport δ)
    (hc : ∀ u ∈ coordinateCube ι 2, ∀ v ∈ coordinateCube ι 2, dist (c u) (c v) = dist u v)
    (hbc : (coordinateCube ι 1).EqOn b c)
    (hflatb : ∀ (T : Finset E) (hT : T.Nonempty), (T : Set E) ⊆ coordinateCube ι 2 →
      δ (T.image b) = meanWidth T hT)
    (hflatc : ∀ (T : Finset E) (hT : T.Nonempty), (T : Set E) ⊆ coordinateCube ι 2 →
      δ (T.image c) = meanWidth T hT)
    (hboth : δ ((coordinateCubeCorners ι 2).image b ∪ (coordinateCubeCorners ι 2).image c) =
      3 * innerCubeWidth ι)
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (s : ℕ → ℝ) (hs : ∀ n, 0 < s n) (h₀ : Tendsto s atTop (𝓝 0))
    (hflatTangent : ∀ y ∈ interior (coordinateCube ι 2), 1 < y i →
      TangentHullWidth E X δ ω hs (c y))
    {z : E} (hz : z ∈ coordinateCube ι 2) :
    FacetOutwardComparison (widthSphereMeasure v₀) i (fun w => dist (c w) (b z)) := by
  have hs' : Tendsto s (ω : Filter ℕ) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨h₀.mono_left hω, Eventually.of_forall hs⟩
  have hcorn : (coordinateCubeCorners ι 1 : Set E) ⊆ coordinateCube ι 2 := by
    refine Subset.trans ?_ (coordinateCube_one_subset_interior_two.trans interior_subset)
    rw [← convexHull_coordinateCubeCorners (ι := ι) (zero_le_one' ℝ)]
    exact subset_convexHull _ _
  apply facetOutwardComparison_of_contracted_prices δ (CATZero.segment hX) c (b z) i v₀ hsub
    hmono (price_insert_catZero_segment hX hsub hmono hpair) hflatc
    (δ (insert (b z) ((coordinateCubeCorners ι 1).image b)) - δ ((coordinateCubeCorners ι 1).image b))
    (fun _ hCT hT => opposite_tip_price_of_corner_prices hsub hmono b c hbc hflatb hflatc hboth hz hCT hT)
    s hs'
  intro y hy hyi _ hdiff M hM
  have hl := tendsto_contractedSites_widthIncrement hX ω hω hs h₀ hc
    (mem_interior_iff_mem_nhds.mp hy) (b z) hdiff.hasGradientAt
    (coordinateCubeCorners ι 1) hcorn (EuclideanSpace.single i (1 : ℝ)) hM.le δ
    (fun p => by simpa using hpair p p) hmove (hflatTangent y hy hyi)
  dsimp only at hl ⊢
  convert hl using 2
  congr!

end Book

end

end SpectralBooks
end LinearAlgebra
end OAI

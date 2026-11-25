import OAI.LinearAlgebra.SpectralBooks.SpectralBookOutward
import OAI.LinearAlgebra.SpectralBooks.PlanarBookConstruction

/-!
# Opening the third page from doubled spectral cubes

The corner price supplied by doubling gives the outward comparison at every
exterior differentiability point. The distance formula identifies the bounded
slabs, and integer magnifications give spectral prices on the entire book.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
section

open Filter Set MeasureTheory HyperbolicObstruction Book
open scoped Topology Classical

variable {K X ι : Type} [Field K] [MetricSpace X] [Fintype ι] [DecidableEq ι]

variable (P : SpectralPlacementPrices K X) (hX : CATZero X) (hjoint : P.JointlyConvexDiagonal hX)
    (b c : (EuclideanSpace ℝ (Option ι)) → X)
    (hb : ∀ u ∈ coordinateCube (Option ι) 2, ∀ v ∈ coordinateCube (Option ι) 2,
      dist (b u) (b v) = dist u v)
    (hc : ∀ u ∈ coordinateCube (Option ι) 2, ∀ v ∈ coordinateCube (Option ι) 2,
      dist (c u) (c v) = dist u v)
    (hbc : (coordinateCube (Option ι) 1).EqOn b c)
    (hboth : P.diagonal ((coordinateCubeCorners (Option ι) 2).image b ∪
      (coordinateCubeCorners (Option ι) 2).image c) = 3 * innerCubeWidth (Option ι))

include P hX hjoint b c hb hc hbc hboth

/-- From the two doubled charts with their combined corner price, obtain
spectral prices over the same field on the full three-page book. -/
theorem exists_book_prices_of_doubled_cubes :
    Nonempty (SpectralPlacementPrices K (Book (EuclideanSpace ℝ ι))) := by
  let e : (EuclideanSpace ℝ (Option ι)) := EuclideanSpace.single none 1
  let v₀ : LiftSphere (EuclideanSpace ℝ (Option ι)) := ⟨horizontal e, mem_sphere_zero_iff_norm.mpr (by simp [e, horizontal])⟩
  let ω : Ultrafilter ℕ := Ultrafilter.of atTop
  let s (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hs (n : ℕ) : 0 < s n := by dsimp [s]; positivity
  have hcmp (p : (EuclideanSpace ℝ (Option ι))) (hp : p ∈ upperUnitCubeFacet none)
      (_ : ∀ j, j ≠ none → p j ∈ Ioo (-1 : ℝ) 1) (r : ℝ) (hr : r ∈ Ioc (0 : ℝ) 1) :
      FacetOutwardComparison (widthSphereMeasure v₀) none (fun w => dist (c w) (b (p + r • e))) := by
    exact spectral_facetOutwardComparison (ι := Option ι) (z := p + r • e)
      P hX hjoint b c none v₀ hb hc hbc hboth ω
      (Ultrafilter.of_le atTop) s hs tendsto_one_div_add_atTop_nhds_zero_nat
      (outward_tip_mem_coordinateCube_two hp ⟨hr.1.le, hr.2⟩)
  obtain ⟨f, hf⟩ := exists_boundedBook_of_outward_comparison (widthSphereMeasure v₀)
    (isCAT0_of_catZero hX) hb hc hbc hcmp
  exact ⟨P.bookOfIsometry f hf⟩

/-- The two-dimensional case supplies actual spectral prices on the scalar-spine
book used in the rectangular matrix multiplication argument. -/
theorem exists_planarBook_prices_of_doubled_squares [Unique ι] :
    Nonempty (SpectralPlacementPrices K (Book ℝ)) := by
  obtain ⟨Q⟩ := exists_book_prices_of_doubled_cubes P hX hjoint b c hb hc hbc hboth
  exact ⟨Q.pullback (planarBookEquiv ι) (planarBookEquiv ι).isometry⟩

end

end

end SpectralBooks
end LinearAlgebra
end OAI

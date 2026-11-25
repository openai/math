import OAI.LinearAlgebra.SpectralBooks.BinaryJointConvexity
import OAI.LinearAlgebra.SpectralBooks.FiniteIntervalExtension
import OAI.LinearAlgebra.SpectralBooks.GridCubeExtension
import OAI.LinearAlgebra.SpectralBooks.SpectralBookConstruction

/-! # From a Euclidean spectral flat to the three-page book

The remaining geometric input asserts that complete geodesic spectral spaces
are CAT(0). Finite midpoint extension, joint convexity of placed diagonals,
and doubling supply the cube charts over the original field.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
section

open HyperbolicObstruction
open scoped Classical

variable {K ι : Type} [Field K] [Fintype ι] [DecidableEq ι]

/-- Theorem `thm:book` from CAT(0) comparison on geodesic spectral spaces.
The index `none` is the normal axis and `ι` indexes the Euclidean spine. -/
theorem exists_book_prices_of_flat
    (H : SpectralPlacementPrices K (EuclideanSpace ℝ (Option ι)))
    (hCN : ∀ (Y : Type) [MetricSpace Y] [CompleteSpace Y],
      SpectralPlacementPrices K Y → IsGeodesic Y → CATZero Y) :
    Nonempty (SpectralPlacementPrices K (Book (EuclideanSpace ℝ ι))) := by
  obtain ⟨Y, m, P, hY, hP, ⟨C⟩⟩ :=
    exists_spectralCubeCharts_of_midpointExtensions H
      SpectralPlacementPrices.exists_finite_midpoint_extension hCN
      (fun P hY => P.jointlyConvexDiagonal_of_raw hY (SiteTensor.rawDiagonalJointConvexity K))
  exact exists_book_prices_of_doubled_cubes P hY hP (C.chart false) (C.chart true)
    (C.dist_eq false) (C.dist_eq true) C.agree C.corner_union

/-- A spectral Euclidean plane supplies the planar book on a scalar spine. -/
theorem exists_planarBook_prices_of_plane
    (H : SpectralPlacementPrices K (EuclideanSpace ℝ (Option Unit)))
    (hCN : ∀ (Y : Type) [MetricSpace Y] [CompleteSpace Y],
      SpectralPlacementPrices K Y → IsGeodesic Y → CATZero Y) :
    Nonempty (SpectralPlacementPrices K (Book ℝ)) := by
  obtain ⟨Q⟩ := exists_book_prices_of_flat H hCN
  exact ⟨Q.pullback (planarBookEquiv Unit) (planarBookEquiv Unit).isometry⟩

end

end

end SpectralBooks
end LinearAlgebra
end OAI

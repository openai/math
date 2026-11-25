import OAI.LinearAlgebra.SpectralBooks.GridCubeConstruction
import OAI.LinearAlgebra.SpectralBooks.GeodesicExtension
import OAI.LinearAlgebra.SpectralBooks.BookFlat

/-! # The geometric hypotheses for opening two cubes

A finite midpoint extension suffices for the complete geodesic enlargement.
When all complete geodesic spectral spaces are CAT(0), this gives the two
charts, and joint convexity gives the flat-law hypothesis of the construction.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open HyperbolicObstruction
section

/-- Real inner product spaces satisfy the squared-distance CAT(0) comparison with equality. -/
theorem innerProductSpace_catZero (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] : CATZero E := by
  intro a b
  refine ⟨AffineMap.lineMap a b, ⟨by simp, by simp, fun s _ t _ ↦ ?_⟩, fun z t ht ↦ ?_⟩
  · rw [dist_lineMap_lineMap, Real.dist_eq]
  · rw [dist_comm z, euclidean_dist_lineMap_sq a b z ht, dist_comm a z, dist_comm b z]

/-- The CAT(0) enlargement required for the finite grids follows from exact finite
midpoint insertion and the CAT(0) property for complete geodesic spectral spaces. -/
theorem HasFiniteMidpointExtensions.exists_catZero_extension {F : Type*} [Field F]
    (h : HasFiniteMidpointExtensions F)
    (hCN : ∀ (Y : Type) [MetricSpace Y] [CompleteSpace Y], SpectralPlacementPrices F Y → IsGeodesic Y → CATZero Y)
    (A : FinitePriceSpace F) (hne : Nonempty A.carrier) :
    ∃ (Y : Type) (_ : MetricSpace Y) (Q : SpectralPlacementPrices F Y), CATZero Y ∧ Nonempty (PriceEmbedding A.prices Q) := by
  obtain ⟨Y, m, Q, e, complete, geo⟩ := h.complete_geodesic_extension A hne.some
  exact ⟨Y, m, Q, hCN Y Q geo, e⟩

/-- The complete doubled-cube and mixed-price conclusions follow from the three general
spectral geometry inputs. Joint convexity supplies the Euclidean flat law at the start.
The finite grids, selected spectral prices, and chart comparisons are constructed internally. -/
theorem exists_spectralCubeCharts_of_midpointExtensions {F ι : Type} [Field F] [Fintype ι] [Nonempty ι]
    (H : SpectralPlacementPrices F (EuclideanSpace ℝ ι)) (hmid : HasFiniteMidpointExtensions F)
    (hCN : ∀ (Y : Type) [MetricSpace Y] [CompleteSpace Y], SpectralPlacementPrices F Y → IsGeodesic Y → CATZero Y)
    (hjoint : ∀ {Y : Type} [MetricSpace Y] (P : SpectralPlacementPrices F Y) (hY : CATZero Y),
      P.JointlyConvexDiagonal hY) :
    ∃ (Y : Type) (_ : MetricSpace Y) (Q : SpectralPlacementPrices F Y) (hY : CATZero Y),
      Q.JointlyConvexDiagonal hY ∧ Nonempty (SpectralCubeCharts ι Q) := by
  apply exists_spectralCubeCharts_of_flat H _ (hmid.exists_catZero_extension hCN) hjoint
  intro S hS
  have hE := innerProductSpace_catZero (EuclideanSpace ℝ ι)
  simpa using H.flatDiagonalLaw_isometry hE (hjoint H hE) isometry_id S hS

end

end SpectralBooks
end LinearAlgebra
end OAI

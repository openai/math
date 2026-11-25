import OAI.LinearAlgebra.SpectralBooks.Fermion.FermionCrossing
import OAI.LinearAlgebra.SpectralBooks.Rigidity
import OAI.LinearAlgebra.SpectralBooks.ShiftedCrossing.ShiftedCost
import OAI.LinearAlgebra.SpectralBooks.WireRecursion

/-! # Curvature of geodesic spectral spaces from the integral crossing identity -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open HyperbolicObstruction

variable {K X : Type*} [Field K] [MetricSpace X]

/-- The two rank bounds for the shifted crossing suffice for the whole CAT(0)
comparison in any geodesic space carrying spectral prices over the field. -/
theorem SpectralPlacementPrices.catZero_of_asymptoticFactorizations
    (P : SpectralPlacementPrices K X) (g : IsGeodesic X)
    (hc : ShiftedCrossing.AsymptoticFactorizations K) : CATZero X := by
  apply P.catZero_of_shiftedCost g P.sectorBusemann _
    (fun _ _ _ _ Q ↦ hc.shiftedCrossingCost Q)
  exact fun o ↦ (Book.blowupSpectralPrices CurvatureBlowup.ultrafilter CurvatureBlowup.scale_pos o
    P).sectorBusemann

/-- Entrywise stabilization of the integral fermion identity gives CAT(0) in
every characteristic, via integral matrix factorizations on the two cuts. -/
theorem SpectralPlacementPrices.catZero_of_truncatedIdentity
    (P : SpectralPlacementPrices K X) (g : IsGeodesic X)
    (hc : Fermion.TruncatedIdentity) : CATZero X :=
  P.catZero_of_asymptoticFactorizations g (Fermion.asymptoticFactorizations_of_truncated hc K)

end SpectralBooks
end LinearAlgebra
end OAI

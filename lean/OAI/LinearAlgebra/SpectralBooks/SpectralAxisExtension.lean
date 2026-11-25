import OAI.LinearAlgebra.SpectralBooks.CharacteristicAlternative
import OAI.LinearAlgebra.SpectralBooks.GeodesicExtension
import OAI.LinearAlgebra.SpectralBooks.Rigidity
import OAI.LinearAlgebra.SpectralBooks.WireRecursion

/-!
# Spectral axis extensions from curvature

The finite midpoint-extension theorem realizes each normalized point in one
complete geodesic spectral space. Curvature of that space suffices for
axis rigidity. Busemann convexity holds for its wires and for rescaled wires
in each blow-up, so the shifted crossing estimate supplies that curvature.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open SiteTensor HyperbolicObstruction

/-- The geodesic extension at scale one preserves the original normalized
point on every tensor on the marked sites. -/
theorem hasSpectralAxisExtensions_of_curvature (K : Type*) [Field K]
    (curv : ∀ (X : Type) [MetricSpace X] [CompleteSpace X], SpectralPlacementPrices K X →
      IsGeodesic X → CATZero X) (D : ℕ) : HasSpectralAxisExtensions.{0} K D := by
  intro φ
  obtain ⟨X, metric, P, y, hc, hg, _, hp⟩ :=
    SpectralPlacementPrices.realize_finite_point_geodesic φ 1 zero_le_one
  let := metric
  let := hc
  refine ⟨X, metric, curv X P hg, P, y, ?_⟩
  intro T _
  have hclass := ofRaw_eq_iff.mpr (Raw.group_id_equivalent T)
  simpa only [Function.comp_id, rawLogPrice, one_mul, hclass] using hp T id

/-- Shifted crossing costs force the curvature needed by every axis
extension. The same synchronized wire estimate applies in each blow-up. -/
theorem hasSpectralAxisExtensions_of_shiftedCost (K : Type*) [Field K]
    (cost : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E],
      SpectralPlacementPrices K E → ShiftedCrossingCost E)
    (D : ℕ) : HasSpectralAxisExtensions.{0} K D := by
  apply hasSpectralAxisExtensions_of_curvature
  intro X _ _ P hg
  apply P.catZero_of_shiftedCost hg P.sectorBusemann _ cost
  intro o
  exact (Book.blowupSpectralPrices CurvatureBlowup.ultrafilter CurvatureBlowup.scale_pos o P).sectorBusemann

universe u

/-- Reduction of the characteristic-wise conclusion to shifted crossing
cost, the Student test for spectral flats, and border stretch for profiled
shortenings. All finite-point extensions are constructed over the same field. -/
theorem characteristicAlternative_of_shiftedCost (K : Type*) [Field K] (p : ℕ) [CharP K p]
    (cost : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E],
      SpectralPlacementPrices K E → ShiftedCrossingCost E)
    (flatTest : ∀ D : ℕ, 2 ≤ D → Nonempty (SpectralPlacementPrices K (EuclideanSpace ℝ (Fin D))) →
      StudentMatrixTest K D)
    (borderStretch : ∀ D : ℕ, 2 ≤ D → Crossing.HasProfileShortening K D →
      ∃ ε : ℝ, 0 < ε ∧ SignedWitnessHardness K ε) : CharacteristicAlternative.{u} p :=
  characteristicAlternative_of_spectral_extensions K p
    (fun D _ => hasSpectralAxisExtensions_of_shiftedCost K cost D) flatTest borderStretch

end SpectralBooks
end LinearAlgebra
end OAI

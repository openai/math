import OAI.LinearAlgebra.SpectralBooks.ArbitrarySpectralExtension
import OAI.LinearAlgebra.SpectralBooks.Curvature
import OAI.LinearAlgebra.SpectralBooks.Fermion.FermionExtract
import OAI.LinearAlgebra.SpectralBooks.Fermion.WickIdentity
import OAI.LinearAlgebra.SpectralBooks.SectorEquality

/-! # Shifted crossings, norm rigidity and spectral CAT(0) extensions -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open HyperbolicObstruction

namespace Fermion

/-- Integral shifted crossing identity on every finite state entry. -/
theorem truncatedIdentity : TruncatedIdentity :=
  truncatedIdentity_of_laurent laurentCrossingIdentity

/-- The integral factorization yields the two shifted crossing ranks over every field. -/
theorem asymptoticFactorizations (K : Type*) [Field K] : ShiftedCrossing.AsymptoticFactorizations K :=
  asymptoticFactorizations_of_truncated truncatedIdentity K

end Fermion

universe u
variable {K : Type*} [Field K] {X : Type u} [MetricSpace X]

/-- Realizing each finite subset of one nonempty open patch up to scale
forces the norm to be induced by an inner product (the manuscript's norm rigidity lemma). -/
theorem HasFiniteSpectralRealizationsOn.innerProductSpace
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {U : Set E} (h : HasFiniteSpectralRealizationsOn K U) (hne : U.Nonempty) (ho : IsOpen U) :
    Nonempty (InnerProductSpace ℝ E) := by
  obtain ⟨Q⟩ := (h.univ_of_open hne ho).prices
  exact ((Fermion.asymptoticFactorizations K).shiftedCrossingCost Q).innerProductSpace

/-- Each finite-dimensional normed space whose finite configurations occur up to scale
in a spectral space has a norm induced by an inner product. -/
theorem SpectralPlacementPrices.normRigidity (P : SpectralPlacementPrices K X) :
    ScaledSectorNormRigidity X :=
  P.normRigidity_of_shiftedCost (fun _ _ _ _ Q ↦ (Fermion.asymptoticFactorizations K).shiftedCrossingCost Q)

/-- The squared midpoint inequality and its whole-segment CAT(0) consequence
hold in any geodesic spectral space over an arbitrary field. -/
theorem SpectralPlacementPrices.catZero (P : SpectralPlacementPrices K X) (g : IsGeodesic X) :
    CATZero X :=
  P.catZero_of_truncatedIdentity g Fermion.truncatedIdentity

/-- Equality in the squared midpoint inequality forces both sectors in the
original spectral space to have the distances of their Euclidean models. -/
theorem SpectralPlacementPrices.sectors_of_midpoint_equality (P : SpectralPlacementPrices K X)
    (g : IsGeodesic X) {m x y z : X} {a b w : ℝ → X}
    (ha : IsSegment a m x) (hb : IsSegment b m y) (hw : IsSegment w m z)
    (hmx : dist m x = dist x y / 2) (hmy : dist m y = dist x y / 2)
    (hsharp : 2 * dist z m ^ 2 + dist x y ^ 2 / 2 = dist z x ^ 2 + dist z y ^ 2) :
    EuclideanSegmentSector g a w m x z ∧ EuclideanSegmentSector g b w m y z := by
  let Q := Book.blowupSpectralPrices CurvatureBlowup.ultrafilter CurvatureBlowup.scale_pos m P
  apply euclideanSegmentSectors_of_midpoint_equality g P.sectorBusemann P.normRigidity _
    ha hb hw hmx hmy hsharp
  apply quadraticRaySectors_of_normRigidity (CurvatureBlowup.isGeodesic g m) Q.sectorBusemann
  intro E _ _ _ model
  obtain ⟨R⟩ := model.spectralPrices Q
  exact ((Fermion.asymptoticFactorizations K).shiftedCrossingCost R).innerProductSpace

/-- A spectral space has a complete CAT(0) extension preserving all its placement prices. -/
theorem SpectralPlacementPrices.exists_complete_catZero_extension (P : SpectralPlacementPrices K X) :
    ∃ (Y : Type u) (_ : MetricSpace Y) (Q : SpectralPlacementPrices K Y),
      Nonempty (PriceEmbedding P Q) ∧ CompleteSpace Y ∧ CATZero Y := by
  obtain ⟨Y, met, Q, e, hY, hg⟩ := P.exists_complete_geodesic_extension_unpointed
  exact ⟨Y, met, Q, e, hY, Q.catZero hg⟩

end SpectralBooks
end LinearAlgebra
end OAI

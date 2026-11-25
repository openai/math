import OAI.LinearAlgebra.SpectralBooks.Theorem
import OAI.LinearAlgebra.SpectralBooks.SpectralBookTheorem
import OAI.LinearAlgebra.SpectralBooks.StudentTestFromBook
import OAI.LinearAlgebra.SpectralBooks.SpectralAxisExtension
import OAI.LinearAlgebra.SpectralBooks.Curvature

/-! # The characteristic alternative from spectral curvature and border stretch -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open HyperbolicObstruction

/-- The finite Student matrix inequality in dimension `D` follows from a
spectral Euclidean `D`-flat using curvature in the doubled-space construction. -/
theorem studentMatrixTest_of_spectral_flat (K : Type) [Field K]
    (hCN : ∀ (X : Type) [MetricSpace X] [CompleteSpace X], SpectralPlacementPrices K X →
      IsGeodesic X → CATZero X)
    {D : ℕ} (hD : 2 ≤ D) (flat : Nonempty (SpectralPlacementPrices K (EuclideanSpace ℝ (Fin D)))) :
    StudentMatrixTest K D := by
  obtain _ | q := D
  · omega
  obtain ⟨P⟩ := flat
  let e := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finSuccEquiv q).symm
  obtain ⟨Q⟩ := exists_book_prices_of_flat (P.pullback e e.isometry) hCN
  exact studentMatrixTest_of_spectral_book K (by omega) Q

universe u

/-- The complete geodesic extension supplies the missing-flat branch, while
a spectral flat supplies the finite Student inequality. Border stretch is
used on exactly the field and profiled shorter crossing produced here. -/
theorem characteristicAlternative_of_spectral_curvature (K : Type) [Field K] (p : ℕ)
    [CharP K p]
    (hCN : ∀ (X : Type) [MetricSpace X] [CompleteSpace X], SpectralPlacementPrices K X →
      IsGeodesic X → CATZero X)
    (borderStretch : ∀ D : ℕ, 2 ≤ D → Crossing.HasProfileShortening K D →
      ∃ ε : ℝ, 0 < ε ∧ SignedWitnessHardness K ε) : CharacteristicAlternative.{u} p :=
  characteristicAlternative_of_spectral_extensions K p
    (fun D _ => hasSpectralAxisExtensions_of_curvature K hCN D)
    (fun _ hD => studentMatrixTest_of_spectral_flat K hCN hD) borderStretch

/-- The integral truncated crossing identity and border stretch for profiled
shortenings suffice over every characteristic. -/
theorem characteristicAlternative_of_truncatedIdentity (K : Type) [Field K] (p : ℕ)
    [CharP K p] (hcross : Fermion.TruncatedIdentity)
    (borderStretch : ∀ D : ℕ, 2 ≤ D → Crossing.HasProfileShortening K D →
      ∃ ε : ℝ, 0 < ε ∧ SignedWitnessHardness K ε) : CharacteristicAlternative.{u} p :=
  characteristicAlternative_of_spectral_curvature K p
    (fun _ _ _ Q hg => Q.catZero_of_truncatedIdentity hg hcross) borderStretch

/-- The companion's border stretch theorem is sufficient for the characteristic-wise
alternative. The finite spectral geometry, Student test, profiled shortening and transfer from
one reference field to all fields of the characteristic are included in the reduction. -/
theorem characteristicAlternative_of_borderStretch (K : Type) [Field K] (p : ℕ) [CharP K p]
    (borderStretch : ∀ D : ℕ, 2 ≤ D → Crossing.HasProfileShortening K D →
      ∃ ε : ℝ, 0 < ε ∧ SignedWitnessHardness K ε) : CharacteristicAlternative.{u} p :=
  characteristicAlternative_of_truncatedIdentity K p Fermion.truncatedIdentity borderStretch

end SpectralBooks
end LinearAlgebra
end OAI

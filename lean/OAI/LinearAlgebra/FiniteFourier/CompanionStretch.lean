import OAI.Computability.BorderVNP.DiagonalPaidColumns
import OAI.LinearAlgebra.FiniteFourier.Companion.CompanionProfile
import OAI.LinearAlgebra.FiniteFourier.CompanionBorder.CompanionBorderSize
import OAI.LinearAlgebra.FiniteFourier.CompanionCNF.CompanionSignedWitnessPresentation
import OAI.LinearAlgebra.FiniteFourier.CharacteristicWitness
import OAI.LinearAlgebra.SpectralBooks.TreeProfileShortening

/-! # Spectral witnesses from the paid-column stretch theorem -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open OAI.LinearAlgebra.SpectralBooks
universe u v

/-- In the tree case the two-dimensional crossing gives a paid identity.
The companion's stretch bound and its signed CNF presentation then give
hard subcubic grids over the same algebraic closure. -/
theorem companion_nonTree (K : Type) [Field K] (q : ℕ) [CharP K q] :
    HasNonTreeWireMetric (AlgebraicClosure K) := by
  by_contra tree
  have short := Companion.profileShortening (D := 2) (by decide) (hasProfileShortening_of_tree tree)
  obtain ⟨ε,hε,lower⟩ := OAI.Computability.BorderVNP.ProvedStretch.profile K q short
  exact tree (CompanionBorder.nonTree_of_pstar_ground
    (CompanionCNF.choicePresentation_Pstar (AlgebraicClosure K)) hε lower)

/-- The rational and prime-field algebraic closures supply a spectral
witness in every characteristic with the same absolute Fourier constant. -/
theorem uniformFourierBorderLower : UniformFourierBorderLower.{u,v} := by
  apply uniformFourierBorderLower_of_characteristic_witnesses
  intro p hp
  rcases hp with prime | rfl
  · let : Fact p.Prime := ⟨prime⟩
    exact ⟨AlgebraicClosure (ZMod p),inferInstance,ringChar.eq _ p,companion_nonTree (ZMod p) p⟩
  · exact ⟨AlgebraicClosure ℚ,inferInstance,ringChar.eq _ 0,companion_nonTree ℚ 0⟩

end FiniteFourier
end LinearAlgebra
end OAI

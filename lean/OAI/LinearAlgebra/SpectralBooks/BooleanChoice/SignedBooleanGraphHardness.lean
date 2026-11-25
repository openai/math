import OAI.LinearAlgebra.SpectralBooks.BooleanChoice.SignedBooleanVerifier
import OAI.LinearAlgebra.SpectralBooks.BooleanChoice.BooleanNetworkChoiceTable
import OAI.LinearAlgebra.SpectralBooks.IndependentSetHardness

/-! # Signed Boolean verifier circuits give hard independent-set grids -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
namespace BooleanChoice
open Filter ExactQuantumFactoring IndependentSetGraph
open scoped BigOperators

theorem choicePresentation_signedWitness {R : Type*} [CommRing R] (h : PolynomialSignedVerifier) :
    HasPolynomialChoicePresentation R (signedWitnessPolynomial R) := by
  obtain ⟨C,b,hC,hb,h⟩ := h
  refine ⟨8 * C,b,by positivity,hb,?_⟩
  filter_upwards [h] with n hn
  obtain ⟨g,c,hsize,hs⟩ := hn
  refine ⟨choiceTable c, ?_, (choiceTable_size c).trans ?_⟩
  · rw [choiceTable_polynomial, signedWitnessPolynomial]
    apply Finset.sum_congr rfl
    intro x _
    rw [← hs, pathCoefficient, Int.cast_sum, map_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro y _
    simp [signedValue, apply_ite Int.cast]
  · simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 8 hsize

theorem hardSubcubicGrids_of_signedVerifier {F : Type*} [Field F]
    (verified : PolynomialSignedVerifier) {ε : ℝ} (hε : 0 < ε) (hard : SignedWitnessHardness F ε) :
    ∃ δ : ℝ, 0 < δ ∧ HardSubcubicGrids F δ :=
  hardSubcubicGrids_of_signedWitness (choicePresentation_signedWitness verified) hε hard

end BooleanChoice

end

end SpectralBooks
end LinearAlgebra
end OAI

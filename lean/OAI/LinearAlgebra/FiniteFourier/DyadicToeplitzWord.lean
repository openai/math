import OAI.LinearAlgebra.FiniteFourier.TriangularToeplitzWord
import OAI.LinearAlgebra.FiniteFourier.GeometricCost
import OAI.LinearAlgebra.FiniteFourier.DyadicFourierNewton

/-! # Occupied-register words for protected Newton factors -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Matrix ExactFourier.CoefficientTime

variable {R : Type*} [CommRing R] {W : Type} [Fintype W] [DecidableEq W] {a d : ℕ}

/-- Additive updates at the same width suffice for all three Newton factors.
The partner array is restored and the ring scalars used for the diagonal
commutator are fixed independently of the input. -/
theorem protectedNewtonFactor_word_of_additive (_ha : 0 < a) (u : Rˣ)
    (hu : ∀ i, 0 < i → i < a → IsUnit ((u : R)^i - 1))
    (hadd : ∀ c : ℤ → R, AdditiveWord W d (toeplitzOfOffsets a c))
    {A : Matrix (Fin a) (Fin a) R} (hA : ProtectedNewtonFactor A) :
    OccupiedWord (Fin a ⊕ W) (6*d+4) A := by
  cases hA with
  | diagonal v hv =>
    exact LayerWord.pad (by omega) ((layerWord_of_layer (layerMatrix_diagonal_units hv)).occupied)
  | lower f hf => exact lowerUnitToeplitz_word_of_units u hu hadd hf
  | upper f hf =>
    rw [truncMatrix_transpose_reindex]
    exact (lowerUnitToeplitz_word_of_units u hu hadd hf).relabel Fin.revPerm

end FiniteFourier
end LinearAlgebra
end OAI

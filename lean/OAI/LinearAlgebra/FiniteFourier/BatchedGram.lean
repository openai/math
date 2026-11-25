import OAI.LinearAlgebra.FiniteFourier.Transform
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-! # The Gram matrix of the doubled Fourier list -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open scoped Matrix

variable {K : Type*} [Field K] {R C : Type*} [Fintype R] [DecidableEq R]

/-- Pairing two copies of the list of input and output columns produces both
orientations of the Fourier matrix in its off-diagonal blocks. -/
theorem augmented_gram (H : Matrix R C K) :
    (Matrix.fromCols 1 H)ᵀ * Matrix.fromCols 1 H =
      Matrix.fromBlocks 1 H Hᵀ (Hᵀ * H) := by
  simp [Matrix.transpose_fromCols]

/-- Fourier orthogonality gives a permutation of the point labels in the lower
diagonal block. The bilinear pairing works in any admissible characteristic. -/
theorem fourier_gram_entry (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (a : Admissible G K) (x y : G) :
    ((fourierMatrix G K)ᵀ * fourierMatrix G K) x y =
      if -x = y then (Fintype.card G : K) else 0 := by
  have h := congrFun (congrFun (inverse_mul_fourier G K a) (-x)) y
  rw [Matrix.mul_apply, Matrix.one_apply] at h
  simp only [inverseFourierMatrix, fourierMatrix, Matrix.of_apply, neg_neg, mul_assoc,
    ← Finset.mul_sum] at h
  rw [Matrix.mul_apply]
  change (∑ χ : Character G K, (χ (.ofAdd x) : K) * (χ (.ofAdd y) : K)) = _
  have hn := a.1
  split_ifs at h ⊢ with heq
  · calc
      _ = (Fintype.card G : K) * ((Fintype.card G : K)⁻¹ *
        ∑ χ : Character G K, (χ (.ofAdd x) : K) * (χ (.ofAdd y) : K)) := by
          rw [← mul_assoc, mul_inv_cancel₀ hn, one_mul]
      _ = _ := by rw [h, mul_one]
  · exact (mul_eq_zero.mp h).resolve_left (inv_ne_zero hn)

end FiniteFourier
end LinearAlgebra
end OAI

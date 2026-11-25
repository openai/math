import OAI.LinearAlgebra.SpectralBooks.AbsoluteTensorRank
import OAI.LinearAlgebra.SpectralBooks.QuotientCircuit

/-! # Specializing a rational matrix multiplication circuit

The decomposition extracted at the generic input satisfies the matrix tensor's
coefficient equations. These equations have a solution of the same length over
the algebraic closure of the ground field, including when that field is finite.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open Foundation

private theorem matrixTensor_map (F L : Type*) [Field F] [Field L] [Algebra F L]
    (a b c : ℕ) :
    (fun x y z => algebraMap F L (matrixTensor F a b c x y z)) = matrixTensor L a b c := by
  funext x y z
  simp [matrixTensor, Tensor.matrixCoefficients, apply_ite]

/-- The matrix tensor over the algebraic closure has rank at most its rank
over the rational function field of the input coordinates. -/
theorem matrix_tensorRank_algebraicClosure_le_fractionRing (F I : Type*) [Field F]
    (a b c : ℕ) :
    tensorRank (matrixTensor (AlgebraicClosure F) a b c) ≤
      tensorRank (matrixTensor (FractionRing (MvPolynomial I F)) a b c) := by
  let K := FractionRing (MvPolynomial I F)
  let : Algebra F K := ((algebraMap (MvPolynomial I F) K).comp MvPolynomial.C).toAlgebra
  have h : Tensor.RankAtMost (fun x y z => algebraMap F K (matrixTensor F a b c x y z))
      (tensorRank (matrixTensor K a b c)) := by
    rw [matrixTensor_map]
    exact rankAtMost_tensorRank _
  apply tensorRank_le_of_rankAtMost
  rw [← matrixTensor_map F (AlgebraicClosure F)]
  exact rankAtMost_of_extension_to_algClosed (AlgebraicClosure F) h

variable {F : Type*} [Field F] {a b c : ℕ} {P : RationalMatrixAlgorithm F a b c}

/-- Each product or quotient contributes at most two simple tensors after
specializing the generic-input decomposition to the algebraic closure. -/
theorem algebraicClosure_rank_le_twice_productQuotientCount (h : P.Correct) :
    tensorRank (matrixTensor (AlgebraicClosure F) b c a) ≤
      2 * P.program.productQuotientCount :=
  (matrix_tensorRank_algebraicClosure_le_fractionRing F (Arithmetic.MatrixInput a b c) b c a).trans
    (matrixTensor_rank_le_twice_productQuotientCount h)

/-- Ordinary rank over the algebraic closure is bounded by twice the formal
arithmetic cost, with division allowed. -/
theorem algebraicClosure_rank_le_twice_cost (h : P.Correct) :
    tensorRank (matrixTensor (AlgebraicClosure F) b c a) ≤ 2 * P.cost :=
  (algebraicClosure_rank_le_twice_productQuotientCount h).trans
    (Nat.mul_le_mul_left 2 P.program.productQuotientCount_le_cost)

end SpectralBooks
end LinearAlgebra
end OAI

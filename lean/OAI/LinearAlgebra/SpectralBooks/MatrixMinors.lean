import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexMatrixTensor
import Mathlib.Data.Matrix.Diagonal

/-! # Identity minors of the matrix multiplication tensor

Fixing the wire opposite a site selects a square submatrix of its flattening
with one row for every local index. The matching-wire rule makes this
submatrix the identity, independently of the scalar characteristic.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open Foundation.Tensor

variable {K A B C : Type*} [CommSemiring K] [DecidableEq A] [DecidableEq B] [DecidableEq C]

/-- Fix the third wire and read off both indices of the first site. -/
theorem matrixMinor₁ (k : C) :
    Matrix.of (fun x x' : A × B =>
      matrixCoefficients (K := K) A B C x (x'.2, k) (k, x'.1)) = 1 := by
  ext x x'
  simp only [Matrix.of_apply, matrixCoefficients, Matrix.one_apply, Prod.ext_iff]
  by_cases ha : x.1 = x'.1 <;> by_cases hb : x.2 = x'.2 <;> simp_all [eq_comm]

/-- Fix the first wire and read off both indices of the second site. -/
theorem matrixMinor₂ (i : A) :
    Matrix.of (fun y y' : B × C =>
      matrixCoefficients (K := K) A B C (i, y'.1) y (y'.2, i)) = 1 := by
  ext y y'
  simp only [Matrix.of_apply, matrixCoefficients, Matrix.one_apply, Prod.ext_iff]
  by_cases hb : y.1 = y'.1 <;> by_cases hc : y.2 = y'.2 <;> simp_all [eq_comm]

/-- Fix the second wire and read off both indices of the third site. -/
theorem matrixMinor₃ (j : B) :
    Matrix.of (fun z z' : C × A =>
      matrixCoefficients (K := K) A B C (z'.2, j) (j, z'.1) z) = 1 := by
  ext z z'
  simp only [Matrix.of_apply, matrixCoefficients, Matrix.one_apply, Prod.ext_iff]
  by_cases hc : z.1 = z'.1 <;> by_cases ha : z.2 = z'.2 <;> simp_all [eq_comm]

end SpectralBooks
end LinearAlgebra
end OAI

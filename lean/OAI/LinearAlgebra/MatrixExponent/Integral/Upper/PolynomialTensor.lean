import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.Coefficients
import OAI.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexPolynomialApproximation
import Lean.Elab.Tactic.Omega

open OAI.LinearAlgebra.MatrixExponent.Integral

/-!
# The polynomial multiplication tensor

The coefficient tensor records ordinary, untruncated polynomial multiplication.
Evaluation at `a + b - 1` distinct field elements and uniform Lagrange
interpolation give an actual rank decomposition of that size.
-/

noncomputable section

open scoped BigOperators
open OAI.MatrixMultiplication.Foundation

namespace OAI.LinearAlgebra.MatrixExponent.Integral.Upper

/-- Multiplication of polynomials with `a` and `b` coefficients, with every
output coefficient retained. -/
def polynomialTensor (a b : ℕ) :
    Tensor O (Fin a) (Fin b) (Fin (a + b - 1)) :=
  fun i j k => if i.val + j.val = k.val then 1 else 0

@[simp] theorem polynomialTensor_apply (a b : ℕ)
    (i : Fin a) (j : Fin b) (k : Fin (a + b - 1)) :
    polynomialTensor a b i j k = if i.val + j.val = k.val then 1 else 0 := rfl

/-- The tensor coefficient is the coefficient of the product of the two input
monomials. -/
theorem polynomialTensor_eq_coeff (a b : ℕ)
    (i : Fin a) (j : Fin b) (k : Fin (a + b - 1)) :
    polynomialTensor a b i j k =
      ((Polynomial.X : Polynomial O) ^ (i.val + j.val)).coeff k.val := by
  simp [polynomialTensor, Polynomial.coeff_X_pow, eq_comm]

/-- Commuting the input factors only reindexes the equal-sized output space. -/
theorem polynomialTensor_swap (a b : ℕ)
    (i : Fin a) (j : Fin b) (k : Fin (a + b - 1)) :
    polynomialTensor a b i j k =
      polynomialTensor b a j i (Fin.cast (by omega) k) := by
  simp [polynomialTensor, Nat.add_comm]

/-- With a scalar as the first input, multiplication is the identity pairing
between the second input and output coefficient coordinates. -/
theorem polynomialTensor_one_left (b : ℕ)
    (i : Fin 1) (j : Fin b) (k : Fin (1 + b - 1)) :
    polynomialTensor 1 b i j k = if j.val = k.val then 1 else 0 := by
  simp [polynomialTensor]

/-- Ordinary polynomial multiplication has an actual decomposition into
`a + b - 1` rank-one tensors. The degenerate empty-input cases are included. -/
theorem polynomialTensor_rankAtMost (a b : ℕ) :
    Tensor.RankAtMost (polynomialTensor a b) (a + b - 1) := by
  classical
  obtain ⟨nodes, hnodes, _⟩ := unit_nodes (a + b - 1)
  refine ⟨(fun t i => nodes t ^ i.val),
    (fun t j => nodes t ^ j.val),
    (fun t k => Integral.weight nodes t k.val), ?_⟩
  funext i j k
  have hsum : i.val + j.val < a + b - 1 := by
    have hi := i.isLt
    have hj := j.isLt
    omega
  have hdegree : ((Polynomial.X : Polynomial O) ^ (i.val + j.val)).degree <
      Fintype.card (Fin (a + b - 1)) := by
    rw [Polynomial.degree_X_pow, Fintype.card_fin]
    exact WithBot.coe_lt_coe.mpr hsum
  have hcoeff := Integral.interpolate nodes hnodes
    ((Polynomial.X : Polynomial O) ^ (i.val + j.val)) k.val hdegree
  rw [polynomialTensor_eq_coeff]
  simpa only [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_mul,
    Tensor.rankOne, pow_add]
    using hcoeff

end OAI.LinearAlgebra.MatrixExponent.Integral.Upper

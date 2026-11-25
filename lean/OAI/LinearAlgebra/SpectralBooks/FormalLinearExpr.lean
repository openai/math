import OAI.LinearAlgebra.SpectralBooks.FormalCircuit
import OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.RecursiveBlockPrograms

/-! # Formal polynomials computed by families of linear expressions -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open Arithmetic Arithmetic.RecursiveBlock MvPolynomial
open scoped BigOperators

noncomputable section

variable {F I O : Type*} [Field F]

private theorem expressionPolynomial_linear_sumFin (n : ℕ) (f : Fin n → Expression F I) :
    expressionPolynomial (LinearExpression.sumFin n f) = ∑ i, expressionPolynomial (f i) := by
  induction n with
  | zero => simp [LinearExpression.sumFin, expressionPolynomial]
  | succ n ih => simp [LinearExpression.sumFin, expressionPolynomial, ih, Fin.sum_univ_succ]

/-- A linear expression compiles to its coefficient-weighted sum of input variables. -/
theorem expressionPolynomial_linear {Term : Type*} [Fintype Term]
    (a : Term → F) (wire : Term → I) :
    expressionPolynomial (LinearExpression.linear a wire) = ∑ i, C (a i) * X (wire i) := by
  rw [LinearExpression.linear, expressionPolynomial_linear_sumFin]
  exact (Fintype.equivFin Term).symm.sum_comp (fun i => C (a i) * X (wire i))

/-- The output polynomial of a compiled family is the polynomial of the selected expression. -/
theorem registerPolynomial_expressions [Fintype O] (e : O → Expression F I) (o : O) :
    registerPolynomial (Family.expressions e).program ((Family.expressions e).output o) =
      expressionPolynomial (e o) :=
  registerPolynomial_compileFamily e o

/-- Each output may sum over its own finite set of input terms. -/
theorem registerPolynomial_expressions_linear [Fintype O] {Term : O → Type*}
    [∀ o, Fintype (Term o)] (a : (o : O) → Term o → F) (wire : (o : O) → Term o → I) (o : O) :
    let p := Family.expressions (fun j => LinearExpression.linear (a j) (wire j))
    registerPolynomial p.program (p.output o) = ∑ i, C (a o i) * X (wire o i) :=
  (registerPolynomial_expressions _ o).trans (expressionPolynomial_linear _ _)

end

end SpectralBooks
end LinearAlgebra
end OAI

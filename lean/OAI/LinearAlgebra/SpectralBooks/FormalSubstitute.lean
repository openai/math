import OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.ProgramComposition
import OAI.LinearAlgebra.SpectralBooks.FormalCircuit
import Mathlib.Algebra.MvPolynomial.Monad

/-! # Formal polynomial semantics of program substitution -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open Arithmetic MvPolynomial

variable {F I J : Type*} [Field F]

private theorem registerPolynomial_substitute_all {r s : ℕ} (p : Program F I r)
    (q : Program F J s) (inputs : J → Fin r) :
    (∀ i, registerPolynomial (p.substitute q inputs).program
      ((p.substitute q inputs).oldOutput i) = registerPolynomial p i) ∧
    (∀ i, registerPolynomial (p.substitute q inputs).program
      ((p.substitute q inputs).output i) =
      bind₁ (fun j => registerPolynomial p (inputs j)) (registerPolynomial q i)) := by
  induction q with
  | nil => exact ⟨fun _ => rfl, fun i => i.elim0⟩
  | step q g ih =>
    obtain ⟨hold, hnew⟩ := ih
    constructor
    · intro i
      cases g <;> exact hold i
    · intro i
      cases g <;> refine Fin.cases ?_ (fun j => hnew j) i <;> simp [gatePolynomial]
      case constant => rfl
      case input j => exact hold (inputs j)
      case add j k => exact congrArg₂ (· + ·) (hnew j) (hnew k)
      case sub j k => exact congrArg₂ (· - ·) (hnew j) (hnew k)
      case mul j k => exact congrArg₂ (· * ·) (hnew j) (hnew k)

/-- Substitution into a program acts on its register polynomials by polynomial substitution. -/
theorem registerPolynomial_substitute {r s : ℕ} (p : Program F I r)
    (q : Program F J s) (inputs : J → Fin r) (j : Fin s) :
    registerPolynomial (p.substitute q inputs).program ((p.substitute q inputs).output j) =
      bind₁ (fun i => registerPolynomial p (inputs i)) (registerPolynomial q j) :=
  (registerPolynomial_substitute_all p q inputs).2 j

end SpectralBooks
end LinearAlgebra
end OAI

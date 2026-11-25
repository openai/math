import OAI.LinearAlgebra.SpectralBooks.FormalLinearExpr
import OAI.LinearAlgebra.SpectralBooks.FormalSubstitute

/-! # Polynomial output of recursive block program families -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open Arithmetic Arithmetic.RecursiveBlock MvPolynomial
noncomputable section

variable {F I J O : Type*} [Field F]

/-- The formal polynomial at a designated output of a circuit family. -/
def familyPolynomial (p : Family F I O) (o : O) : MvPolynomial I F :=
  registerPolynomial p.program (p.output o)

/-- Composition of circuit families substitutes the inner output polynomials. -/
theorem familyPolynomial_compose (p : Family F I J) (q : Family F J O) (o : O) :
    familyPolynomial (p.compose q) o =
      bind₁ (familyPolynomial p) (familyPolynomial q o) :=
  registerPolynomial_substitute p.program q.program p.output (q.output o)

theorem registerPolynomial_mapInput (f : I → J) {r : ℕ}
    (p : Program F I r) (i : Fin r) :
    registerPolynomial (p.mapInput f) i = rename f (registerPolynomial p i) := by
  induction p with
  | nil => exact i.elim0
  | step p g ih =>
    refine Fin.cases ?_ (fun j => ih j) i
    cases g <;> simp [Program.mapInput, Gate.mapInput, gatePolynomial, ih]

private theorem familyPolynomial_parallel (r : ℕ) (p : Fin r → Family F I O)
    (o : Fin r × O) :
    familyPolynomial (Family.parallel r p) o = familyPolynomial (p o.1) o.2 := by
  induction r with
  | zero => exact o.1.elim0
  | succ r ih =>
    rcases o with ⟨i, o⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · exact registerPolynomial_append_old _ _ _
    · exact (registerPolynomial_append_new _ _ _).trans (ih _ (j, o))

/-- A copy of a circuit renames each variable by attaching its copy index. -/
theorem familyPolynomial_copies (r : ℕ) (p : Family F I O) (o : Fin r × O) :
    familyPolynomial (Family.copies r p) o =
      rename (fun i => (o.1, i)) (familyPolynomial p o.2) := by
  rw [Family.copies, familyPolynomial_parallel]
  exact registerPolynomial_mapInput _ _ _

theorem familyPolynomial_ofMatrix {a b c : ℕ} (p : MatrixAlgorithm F a b c)
    (o : Fin a × Fin c) :
    familyPolynomial (Family.ofMatrix p) o = registerPolynomial p.program (p.output o.1 o.2) :=
  rfl

/-- Compiling a family of expressions computes their formal polynomials. -/
theorem familyPolynomial_expressions [Fintype O] (e : O → Expression F I) (o : O) :
    familyPolynomial (Family.expressions e) o = expressionPolynomial (e o) :=
  registerPolynomial_expressions e o

variable {n₁ n₂ n₃ r m₁ m₂ m₃ : ℕ}

theorem familyPolynomial_inputFamily_left
    (a : Fin r → Fin n₁ × Fin n₂ → F) (b : Fin r → Fin n₂ × Fin n₃ → F)
    (q : Fin r) (s : Fin m₁) (t : Fin m₂) :
    familyPolynomial (inputFamily (m₃ := m₃) a b) (q, .inl (s, t)) =
      ∑ x, C (a q x) * X (.inl (join x.1 s, join x.2 t)) := by
  rw [inputFamily, familyPolynomial_expressions, inputExpressions, expressionPolynomial_linear]

theorem familyPolynomial_inputFamily_right
    (a : Fin r → Fin n₁ × Fin n₂ → F) (b : Fin r → Fin n₂ × Fin n₃ → F)
    (q : Fin r) (t : Fin m₂) (u : Fin m₃) :
    familyPolynomial (inputFamily (m₁ := m₁) a b) (q, .inr (t, u)) =
      ∑ y, C (b q y) * X (.inr (join y.1 t, join y.2 u)) := by
  rw [inputFamily, familyPolynomial_expressions, inputExpressions, expressionPolynomial_linear]

/-- Substitution into the output linear combinations joins the two output indices. -/
theorem bind₁_outputFamily {V : Type*} (c : Fin r → Fin n₃ × Fin n₁ → F)
    (v : Fin r × (Fin m₁ × Fin m₃) → MvPolynomial V F)
    (i : Fin n₁) (k : Fin n₃) (s : Fin m₁) (u : Fin m₃) :
    bind₁ v (familyPolynomial (outputFamily c) (join i s, join k u)) =
      ∑ q, C (c q (k, i)) * v (q, (s, u)) := by
  simp only [outputFamily, familyPolynomial_expressions, outputExpressions,
    expressionPolynomial_linear, join, Equiv.symm_apply_apply, map_sum, map_mul,
    bind₁_C_right, bind₁_X_right]

/-- The formal products of the input block linear combinations computed by recursive copies. -/
theorem familyPolynomial_recursiveProducts
    (a : Fin r → Fin n₁ × Fin n₂ → F) (b : Fin r → Fin n₂ × Fin n₃ → F)
    (P : MatrixAlgorithm F m₁ m₂ m₃) (hP : FormalCorrect P)
    (q : Fin r) (s : Fin m₁) (u : Fin m₃) :
    familyPolynomial (recursiveProducts a b P) (q, (s, u)) =
      ∑ t : Fin m₂,
        (∑ x, C (a q x) * X (.inl (join x.1 s, join x.2 t))) *
        (∑ y, C (b q y) * X (.inr (join y.1 t, join y.2 u))) := by
  rw [recursiveProducts, familyPolynomial_compose, familyPolynomial_copies,
    familyPolynomial_ofMatrix, hP, bind₁_rename, map_sum]
  simp only [map_mul, bind₁_X_right, Function.comp_apply, familyPolynomial_inputFamily_left,
    familyPolynomial_inputFamily_right]

end

end SpectralBooks
end LinearAlgebra
end OAI

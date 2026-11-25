import OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.NaiveAlgorithm

/-! # Formal polynomial semantics for division-free arithmetic circuits

Registers in the repository's straight-line programs can be interpreted in the
polynomial ring on the inputs. This distinguishes formal identities over a finite
field from equality of polynomial functions on its rational points.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open Arithmetic MvPolynomial
open scoped BigOperators
noncomputable section

variable {F I R : Type*} [CommRing F]

/-- The polynomial produced at one gate from the polynomials in its registers. -/
def gatePolynomial (g : Gate F I R) (v : R → MvPolynomial I F) : MvPolynomial I F :=
  g.casesOn (fun c => C c) (fun i => X i)
    (fun i j => v i + v j) (fun i j => v i - v j) (fun i j => v i * v j)

/-- Formal polynomial in each register of a straight-line program. -/
def registerPolynomial : {r : ℕ} → Program F I r → Fin r → MvPolynomial I F
  | _, .nil => Fin.elim0
  | _, .step p g => Fin.cases (gatePolynomial g (registerPolynomial p)) (registerPolynomial p)

@[simp] theorem registerPolynomial_zero {r : ℕ} (p : Program F I r) (g : Gate F I (Fin r)) :
    registerPolynomial (p.step g) 0 = gatePolynomial g (registerPolynomial p) := rfl

@[simp] theorem registerPolynomial_succ {r : ℕ} (p : Program F I r) (g : Gate F I (Fin r))
    (i : Fin r) : registerPolynomial (p.step g) i.succ = registerPolynomial p i := rfl

/-- Formal correctness in the paper, including over a finite ground field. -/
def FormalCorrect {a b c : ℕ} (P : MatrixAlgorithm F a b c) : Prop :=
  ∀ i k, registerPolynomial P.program (P.output i k) =
    ∑ j : Fin b, X (Sum.inl (i, j)) * X (Sum.inr (j, k))

private theorem gatePolynomial_mapRegister {S : Type*} (f : R → S)
    (v : S → MvPolynomial I F) (g : Gate F I R) :
    gatePolynomial (g.mapRegister f) v = gatePolynomial g (v ∘ f) := by
  cases g <;> rfl

theorem registerPolynomial_append_new {r s : ℕ} (p : Program F I r)
    (q : Program F I s) (i : Fin s) :
    registerPolynomial (p.append q) (Program.newIndex r s i) = registerPolynomial q i := by
  induction q with
  | nil => exact i.elim0
  | @step s q g ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Program.append, Program.newIndex_zero, registerPolynomial_zero,
        gatePolynomial_mapRegister]
      congr 1
      exact funext ih
    · simpa only [Program.append, Program.newIndex_succ, registerPolynomial_succ] using ih j

theorem registerPolynomial_append_old {r s : ℕ} (p : Program F I r)
    (q : Program F I s) (i : Fin r) :
    registerPolynomial (p.append q) (Program.oldIndex r s i) = registerPolynomial p i := by
  induction q with
  | nil => simp [Program.append]
  | @step s q g ih =>
    simpa only [Program.append, Program.oldIndex_succ, registerPolynomial_succ] using ih

end

noncomputable section

variable {F I : Type*} [Field F]

-- Keep the matcher name exported by earlier builds of this module.
set_option linter.auxLemma false in
abbrev expressionPolynomial.match_1 := @Expression.cost.match_1

theorem registerPolynomial_compile (e : Expression F I) :
    registerPolynomial e.compile.program e.compile.output = expressionPolynomial e := by
  induction e <;> simp_all [Expression.compile, expressionPolynomial, gatePolynomial,
    registerPolynomial_append_old, registerPolynomial_append_new]

private theorem registerPolynomial_compileFinFamily (n : ℕ) (f : Fin n → Expression F I)
    (i : Fin n) :
    registerPolynomial (Expression.compileFinFamily n f).program
      ((Expression.compileFinFamily n f).output i) = expressionPolynomial (f i) := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [Expression.compileFinFamily, registerPolynomial_append_old, registerPolynomial_compile]
    · simp [Expression.compileFinFamily, registerPolynomial_append_new, ih]

theorem registerPolynomial_compileFamily {O : Type*} [Fintype O]
    (f : O → Expression F I) (i : O) :
    registerPolynomial (Expression.compileFamily f).program ((Expression.compileFamily f).output i)
      = expressionPolynomial (f i) := by
  simp [Expression.compileFamily, registerPolynomial_compileFinFamily]

theorem expressionPolynomial_sumFin {n : ℕ} (f : Fin n → Expression F I) :
    expressionPolynomial (Expression.sumFin f) = ∑ i, expressionPolynomial (f i) := by
  induction n with
  | zero => simp [Expression.sumFin, expressionPolynomial]
  | succ n ih => simp [Expression.sumFin, expressionPolynomial, ih, Fin.sum_univ_succ]

/-- The usual entrywise algorithm computes the formal matrix product over every field. -/
theorem formalCorrect_naiveAlgorithm (F : Type*) [Field F] (a b c : ℕ) :
    FormalCorrect (naiveAlgorithm (F := F) a b c) := by
  intro i k
  simp [naiveAlgorithm, registerPolynomial_compileFamily, naiveEntry, expressionPolynomial_sumFin,
    expressionPolynomial]

end

end SpectralBooks
end LinearAlgebra
end OAI

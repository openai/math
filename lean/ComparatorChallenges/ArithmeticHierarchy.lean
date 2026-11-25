import Mathlib

/-! # Strict inclusions of nonuniform arithmetic complexity classes -/

namespace OAI

namespace Computability.VPVNP.Valiant.Project

open scoped Classical

/-- A table of `s` binary gates computes `p`. Variables and scalars are free, and the
output and later gates may reuse any previously available value. -/
def Computes {F σ : Type*} [Field F] (s : ℕ) (p : MvPolynomial σ F) : Prop :=
  ∃ v : Fin s → MvPolynomial σ F,
    let available (k : ℕ) (x : MvPolynomial σ F) :=
      (∃ j : σ, MvPolynomial.X j = x) ∨ (∃ a : F, MvPolynomial.C a = x) ∨
        ∃ j : Fin s, j.val < k ∧ v j = x
    available s p ∧ ∀ i : Fin s, ∃ a b, available i.val a ∧ available i.val b ∧
      (v i = a + b ∨ v i = a - b ∨ v i = a * b)

/-- A polynomial bound uniform in all sufficiently large indices. -/
def PolynomiallyBounded (f : ℕ → ℕ) : Prop := ∃ A d N : ℕ, ∀ n ≥ N, f n ≤ A * n ^ d

/-- At each index a family has its own finite type of indeterminates. -/
abbrev Family (F : Type*) [Field F] (σ : ℕ → Type) := (n : ℕ) → MvPolynomial (σ n) F

variable {F : Type*} [Field F] {σ : ℕ → Type} [∀ n, Fintype (σ n)]

/-- Arity and total degree grow at most polynomially with the index. -/
def PFamily (p : Family F σ) : Prop :=
  PolynomiallyBounded (fun n => Fintype.card (σ n)) ∧
    PolynomiallyBounded (fun n => (p n).totalDegree)

/-- VP consists of polynomial families computed by polynomial-size exact circuits. -/
def IsVP (p : Family F σ) : Prop :=
  PFamily p ∧ ∃ s : ℕ → ℕ, PolynomiallyBounded s ∧ ∀ n, Computes (s n) (p n)

/-- A VNP family sums a VP verifier over all Boolean assignments to its witness variables. -/
def IsVNP (p : Family F σ) : Prop :=
  PFamily p ∧ ∃ (W : ℕ → Type) (inst : ∀ n, Fintype (W n)) (g : Family F (fun n => σ n ⊕ W n)),
    PolynomiallyBounded (fun n => @Fintype.card _ (inst n)) ∧ IsVP g ∧ ∀ n,
      p n = ∑ y : W n → Bool, MvPolynomial.eval₂Hom MvPolynomial.C
        (Sum.elim MvPolynomial.X (fun i => MvPolynomial.C (if y i then 1 else 0))) (g n)

end Computability.VPVNP.Valiant.Project

namespace Computability.VPVNP

def PolynomiallyBounded (f : ℕ → ℕ) : Prop :=
  ∃ A d N : ℕ, ∀ n ≥ N, f n ≤ A * n ^ d

variable {F : Type*} [Field F] {σ : ℕ → Type} [∀ n, Fintype (σ n)]

/-- A sequence of formal polynomials over `F` whose variable type `σ n` may depend on the index
`n`. -/
abbrev Family (F : Type*) [CommSemiring F] (σ : ℕ → Type) :=
  (n : ℕ) → MvPolynomial (σ n) F

/-- Both the number of variables and the total degree of the indexed polynomials are
polynomially bounded in the family index. -/
def PFamily (p : Family F σ) : Prop :=
  PolynomiallyBounded (fun n => Fintype.card (σ n)) ∧
    PolynomiallyBounded (fun n => (p n).totalDegree)

end Computability.VPVNP

namespace MatrixMultiplication.Arithmetic

inductive Expression (F Input : Type*) where
  | constant : F → Expression F Input
  | input : Input → Expression F Input
  | add : Expression F Input → Expression F Input → Expression F Input
  | sub : Expression F Input → Expression F Input → Expression F Input
  | mul : Expression F Input → Expression F Input → Expression F Input

namespace Expression

variable {F Input : Type*}

def cost : Expression F Input → ℕ
  | .constant _ => 0
  | .input _ => 0
  | .add e f => e.cost + f.cost + 1
  | .sub e f => e.cost + f.cost + 1
  | .mul e f => e.cost + f.cost + 1

end Expression
end MatrixMultiplication.Arithmetic

namespace LinearAlgebra.SpectralBooks

open MatrixMultiplication.Arithmetic MvPolynomial
noncomputable section

variable {F I : Type*} [Field F]

def expressionPolynomial : Expression F I → MvPolynomial I F
  | .constant z => C z
  | .input i => X i
  | .add e f => expressionPolynomial e + expressionPolynomial f
  | .sub e f => expressionPolynomial e - expressionPolynomial f
  | .mul e f => expressionPolynomial e * expressionPolynomial f

end
end LinearAlgebra.SpectralBooks

namespace Hierarchy
universe u
open scoped BigOperators
noncomputable section

abbrev Formula (F : Type u) (σ : Type) := MatrixMultiplication.Arithmetic.Expression F σ

/-- The formal polynomial computed by the expression tree. -/
abbrev Formula.polynomial {F : Type*} {σ : Type} [Field F] (f : Formula F σ) : MvPolynomial σ F :=
  LinearAlgebra.SpectralBooks.expressionPolynomial f

/-- The independent scalar coefficients of an affine-linear edge label. -/
structure Affine (F : Type u) (σ : Type) where
  constant : F
  coeff : σ → F

namespace Affine
variable {F : Type*} {σ : Type} [CommSemiring F]

def polynomial [Fintype σ] (l : Affine F σ) : MvPolynomial σ F :=
  MvPolynomial.C l.constant + ∑ i, MvPolynomial.C (l.coeff i) * MvPolynomial.X i

end Affine

/-- A DAG in topological order. A row with no incoming edges has value zero. -/
inductive Rows (F : Type u) (σ : Type) : ℕ → Type u where
  | source : Rows F σ 1
  | snoc {n : ℕ} (prev : Rows F σ n) (edges : List (Fin n × Affine F σ)) : Rows F σ (n + 1)

namespace Rows
variable {F : Type*} {σ : Type}

def edgeCount : {n : ℕ} → Rows F σ n → ℕ
  | _, .source => 0
  | _, .snoc prev edges => prev.edgeCount + edges.length

def values [CommSemiring F] [Fintype σ] : {n : ℕ} → Rows F σ n → Fin n → MvPolynomial σ F
  | _, .source => fun _ => 1
  | _, .snoc prev edges =>
      Fin.lastCases ((edges.map (fun e => prev.values e.1 * e.2.polynomial)).sum) prev.values

end Rows

/-- A finite topologically ordered branching program with a designated sink. -/
structure ABP (F : Type u) (σ : Type) where
  vertices : ℕ
  rows : Rows F σ vertices
  sink : Fin vertices

def ABP.size {F : Type*} {σ : Type} (g : ABP F σ) : ℕ := g.vertices + g.rows.edgeCount

def ABP.polynomial {F : Type*} {σ : Type} [CommSemiring F] [Fintype σ] (g : ABP F σ) : MvPolynomial σ F :=
  g.rows.values g.sink

variable {F : Type*} [Field F] {σ : ℕ → Type} [∀ n, Fintype (σ n)]

/-- Polynomial-size formulas computing the terms of a polynomial family. -/
def IsVF (p : Computability.VPVNP.Family F σ) : Prop :=
  Computability.VPVNP.PFamily p ∧ ∃ f : ∀ n, Formula F (σ n),
    (∀ n, (f n).polynomial = p n) ∧ Computability.VPVNP.PolynomiallyBounded (fun n => (f n).cost)

/-- Polynomial-size affine branching programs computing the terms of a polynomial family. -/
def IsVBP (p : Computability.VPVNP.Family F σ) : Prop :=
  Computability.VPVNP.PFamily p ∧ ∃ g : ∀ n, ABP F (σ n),
    (∀ n, (g n).polynomial = p n) ∧ Computability.VPVNP.PolynomiallyBounded (fun n => (g n).size)

end
end Hierarchy


namespace Hierarchy

/-- The variable set can change with the family index. The four class predicates
below impose the polynomial bounds on arity, degree and computational size. -/
structure PolynomialFamily (F : Type*) [Field F] where
  varsAt : ℕ → Type
  finiteVariables : ∀ n, Fintype (varsAt n)
  polynomials : Computability.VPVNP.Family F varsAt

attribute [instance] PolynomialFamily.finiteVariables

def VF (F : Type*) [Field F] : Set (PolynomialFamily F) := {p | IsVF p.polynomials}

def VBP (F : Type*) [Field F] : Set (PolynomialFamily F) := {p | IsVBP p.polynomials}

end Hierarchy
end OAI

namespace OAI
namespace Hierarchy
namespace Valiant

open Computability.VPVNP.Valiant.Project

/-- Polynomial families computed by polynomial-size exact circuits. -/
def VP (F : Type*) [Field F] : Set (PolynomialFamily F) :=
  {p | IsVP p.polynomials}

/-- Polynomial families obtained by Boolean summation of a VP verifier. -/
def VNP (F : Type*) [Field F] : Set (PolynomialFamily F) :=
  {p | IsVNP p.polynomials}

/-- Each consecutive pair of arithmetic classes is strictly separated over the same field. -/
theorem strict_inclusions (F : Type*) [Field F] :
    VF F ⊂ VBP F ∧ VBP F ⊂ VP F ∧ VP F ⊂ VNP F := by
  sorry

end Valiant
end Hierarchy
end OAI

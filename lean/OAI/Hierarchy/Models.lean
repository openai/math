import OAI.Computability.VPVNP.Classes
import OAI.LinearAlgebra.SpectralBooks.FormalCircuit
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

namespace OAI
/-! # Arithmetic formulas and affine algebraic branching programs

The source vertex of a branching program carries the constant one. Adding a
vertex gives its list of incoming labelled edges, one for each occurrence
including parallel edges. The value stored at each vertex is the sum of the
label products over paths to it, grouped by their final edge.
-/

namespace Hierarchy
universe u
open scoped BigOperators
noncomputable section

abbrev Formula (F : Type u) (σ : Type) := MatrixMultiplication.Arithmetic.Expression F σ

/-- The formal polynomial computed by the expression tree. -/
abbrev Formula.polynomial {F : Type*} {σ : Type} [Field F] (f : Formula F σ) : MvPolynomial σ F :=
  LinearAlgebra.SpectralBooks.expressionPolynomial f

/-- At most `s` binary operation gates, with arbitrary scalar or variable leaves. -/
def HasFormula {F : Type*} {σ : Type} [Field F] (s : ℕ) (p : MvPolynomial σ F) : Prop :=
  ∃ f : Formula F σ, f.polynomial = p ∧ f.cost ≤ s

/-- The independent scalar coefficients of an affine-linear edge label. -/
structure Affine (F : Type u) (σ : Type) where
  constant : F
  coeff : σ → F

namespace Affine
variable {F : Type*} {σ : Type} [CommSemiring F]

def polynomial [Fintype σ] (l : Affine F σ) : MvPolynomial σ F :=
  MvPolynomial.C l.constant + ∑ i, MvPolynomial.C (l.coeff i) * MvPolynomial.X i

def ofScalar (c : F) : Affine F σ := ⟨c, fun _ => 0⟩

def ofVariable (j : σ) : Affine F σ := by
  classical
  exact ⟨0, fun i => if i = j then 1 else 0⟩

@[simp] theorem polynomial_ofScalar [Fintype σ] (c : F) :
    (ofScalar (σ := σ) c).polynomial = MvPolynomial.C c := by
  simp [polynomial, ofScalar]

@[simp] theorem polynomial_ofVariable [Fintype σ] (j : σ) :
    (ofVariable (F := F) j).polynomial = MvPolynomial.X j := by
  classical
  simp [polynomial, ofVariable, apply_ite, ite_mul]

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

/-- Vertices and edges together use at most `s` units of size. -/
def HasABP {F : Type*} {σ : Type} [Field F] [Fintype σ] (s : ℕ) (p : MvPolynomial σ F) : Prop :=
  ∃ g : ABP F σ, g.polynomial = p ∧ g.size ≤ s

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

end OAI

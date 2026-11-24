import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.CharP.Basic
import Mathlib.LinearAlgebra.Matrix.Permanent

/-! # Permanent completeness for exact arithmetic circuits -/

namespace OAI
namespace Computability
namespace VPVNP

namespace Valiant.Project

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

variable {F : Type*} [Field F] {σ τ : ℕ → Type} [∀ n, Fintype (σ n)]

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

/-- A p-projection substitutes target variables or scalars at polynomially bounded indices. -/
def PProjects (target : Family F τ) (source : Family F σ) : Prop :=
  ∃ r : ℕ → ℕ, PolynomiallyBounded r ∧ ∀ n, ∃ φ : σ (r n) → τ n ⊕ F,
    MvPolynomial.eval₂Hom MvPolynomial.C (fun i => (φ i).elim MvPolynomial.X MvPolynomial.C)
      (source (r n)) = target n

/-- Membership in VNP and hardness for every VNP family over the same field. -/
def VNPComplete (p : Family F σ) : Prop :=
  IsVNP p ∧ ∀ (τ : ℕ → Type) [∀ n, Fintype (τ n)] (g : Family F τ), IsVNP g → PProjects g p

/-- The permanent of the generic square matrix of formal variables. -/
noncomputable def permanent (F : Type*) [Field F] (n : ℕ) : MvPolynomial (Fin n × Fin n) F :=
  Matrix.permanent (Matrix.of fun i j => MvPolynomial.X (i, j))

end Valiant.Project

end VPVNP
end Computability
end OAI

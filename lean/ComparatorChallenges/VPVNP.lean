import Mathlib

/-! # Exact VP and VNP over every field -/

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

namespace Computability.VPVNP.Standalone

universe u

/-- The two nonuniform classes differ over each field. -/
theorem vp_ne_vnp (F : Type u) [Field F] :
    (Valiant.Project.IsVP : Valiant.Project.Family F (fun n => Fin n × Bool) → Prop) ≠
      Valiant.Project.IsVNP := by
  sorry

end Computability.VPVNP.Standalone

end OAI

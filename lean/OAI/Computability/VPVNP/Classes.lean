import OAI.Computability.VPVNP.CircuitSize
import OAI.Computability.VPVNP.EventualBounds

/-! # Nonuniform arithmetic complexity classes

A family is indexed by its length. Its variables may be any finite type at that length.
The bounds are asymptotic, with an exponent and a leading constant independent of the
length. Circuits compute formal polynomials, and only Boolean witness variables are
specialized to field elements in the definition of VNP.
-/

namespace OAI
namespace Computability
namespace VPVNP

open scoped Classical

/-- There are fixed natural numbers `A`, `d` and `N` such that `f n ≤ A * n^d` for every `n ≥
N`. -/
def PolynomiallyBounded (f : ℕ → ℕ) : Prop :=
  ∃ A d N : ℕ, ∀ n ≥ N, f n ≤ A * n ^ d

variable {F : Type*} [Field F] {σ τ : ℕ → Type} [∀ n, Fintype (σ n)]

/-- A sequence of formal polynomials over `F` whose variable type `σ n` may depend on the index
`n`. -/
abbrev Family (F : Type*) [CommSemiring F] (σ : ℕ → Type) :=
  (n : ℕ) → MvPolynomial (σ n) F

/-- Both the number of variables and the total degree of the indexed polynomials are
polynomially bounded in the family index. -/
def PFamily (p : Family F σ) : Prop :=
  PolynomiallyBounded (fun n => Fintype.card (σ n)) ∧
    PolynomiallyBounded (fun n => (p n).totalDegree)

/-- The family has polynomially bounded variable count and degree, and each member is computed
exactly as a formal polynomial by arithmetic circuits of polynomially bounded size with
arbitrary field constants. -/
def IsVP (p : Family F σ) : Prop :=
  PFamily p ∧ PolynomiallyBounded (fun n => circuitSize (p n))

/-- Substitution of the bits of a single witness, leaving the output variables formal. -/
noncomputable def witnessValue {X W : Type} (bits : W → Bool) :
    MvPolynomial (X ⊕ W) F →+* MvPolynomial X F :=
  MvPolynomial.eval₂Hom MvPolynomial.C (Sum.elim MvPolynomial.X
    (fun i => MvPolynomial.C (if bits i then 1 else 0)))

/-- A polynomial family obtained by summing a VP family over all Boolean assignments to a
polynomially bounded number of witness variables, with the output variables left formal. -/
def IsVNP (p : Family F σ) : Prop :=
  PFamily p ∧ ∃ (W : ℕ → Type) (inst : ∀ n, Fintype (W n))
    (g : Family F (fun n => σ n ⊕ W n)),
    PolynomiallyBounded (fun n => @Fintype.card _ (inst n)) ∧ IsVP g ∧
    ∀ n, p n = ∑ y : W n → Bool, witnessValue y (g n)

/-- The source index can grow polynomially and need not be monotone. -/
def PProjects (target : Family F τ) (source : Family F σ) : Prop :=
  ∃ r : ℕ → ℕ, PolynomiallyBounded r ∧
    ∀ n, ∃ φ : Projection F (σ (r n)) (τ n), φ.hom (source (r n)) = target n

/-- The family belongs to VNP and every VNP family over the same field is obtained from it by a
polynomially bounded reindexing and substitutions of variables by target variables or field
constants. -/
def VNPComplete (p : Family F σ) : Prop :=
  IsVNP p ∧ ∀ (τ : ℕ → Type) [∀ n, Fintype (τ n)] (g : Family F τ), IsVNP g → PProjects g p

/-- The strict lower bound required in Theorem 1.1 excludes membership in VP. -/
theorem not_isVP_of_eventual_size {p : Family F σ}
    (h : EventuallySuperpolynomial (fun n => circuitSize (p n))) : ¬ IsVP p :=
  fun hp => h.not_polynomially_bounded hp.2

end VPVNP
end Computability
end OAI

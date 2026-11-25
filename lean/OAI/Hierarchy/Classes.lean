import OAI.Hierarchy.Models

namespace OAI
/-! # The four classes as sets of formal polynomial families -/

namespace Hierarchy

/-- The variable set can change with the family index. The four class predicates
below impose the polynomial bounds on arity, degree and computational size. -/
structure PolynomialFamily (F : Type*) [Field F] where
  varsAt : ℕ → Type
  finiteVariables : ∀ n, Fintype (varsAt n)
  polynomials : Computability.VPVNP.Family F varsAt

attribute [instance] PolynomialFamily.finiteVariables

namespace PolynomialFamily

/-- Bundle an existing family with its own finite variable types. -/
def ofFamily {F : Type*} [Field F] {σ : ℕ → Type} [inst : ∀ n, Fintype (σ n)]
    (p : Computability.VPVNP.Family F σ) : PolynomialFamily F := ⟨σ, inst, p⟩

end PolynomialFamily

def VF (F : Type*) [Field F] : Set (PolynomialFamily F) := {p | IsVF p.polynomials}

def VBP (F : Type*) [Field F] : Set (PolynomialFamily F) := {p | IsVBP p.polynomials}

def VP (F : Type*) [Field F] : Set (PolynomialFamily F) := {p | Computability.VPVNP.IsVP p.polynomials}

def VNP (F : Type*) [Field F] : Set (PolynomialFamily F) := {p | Computability.VPVNP.IsVNP p.polynomials}

end Hierarchy

end OAI

import OAI.Hierarchy.Classes
import OAI.Computability.VPVNP.Valiant.Project

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

theorem vp_eq (F : Type*) [Field F] : VP F = Hierarchy.VP F :=
  Set.ext fun p => isVP_iff p.polynomials

theorem vnp_eq (F : Type*) [Field F] : VNP F = Hierarchy.VNP F :=
  Set.ext fun p => isVNP_iff p.polynomials

end Valiant
end Hierarchy
end OAI

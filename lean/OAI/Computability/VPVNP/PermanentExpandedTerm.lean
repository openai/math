import OAI.Computability.VPVNP.PermanentGraph

/-!
# Expanding the rows outside the equality gadgets

A term chooses a direction in each variable-ring row and an occurrence in
each clause row. The internal gadget rows are kept together until their
three squarefree column coefficients are extracted.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PermanentReduction

open MvPolynomial

variable {k m c : ℕ} {R : Type*} [CommRing R]

/-- The summand associated to the choices in all exterior rows. -/
noncomputable def expandedTerm (occ : Fin m → Fin k × Fin c × Bool) (w : Fin k → R)
    (b : R) (a : RingRow k m → Bool) (y : Fin c → Fin m) :
    MvPolynomial (Interior m) (MvPolynomial (Exterior k m c) R) :=
  (∏ g, rename (Prod.mk g) (equalityRows (C b) (X (ringExit occ g)) (X (clauseExit occ g)))) *
    (∏ u, C (C (ringWeight w u (a u))) *
      sumAlgEquiv R (Interior m) (Exterior k m c) (X (ringEntry occ u (a u)))) *
    (∏ i, if (occ (y i)).2.1 = i then X (y i, 1) else 0)

end PermanentReduction

end VPVNP
end Computability
end OAI

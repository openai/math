import OAI.Computability.VPVNP.PermanentGraph

/-!
# Direct ring edges

An unmarked edge contributes its destination column immediately. A marked edge
acquires its exterior column when the occurrence gadget uses its ring exit.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PermanentReduction

open MvPolynomial

/-- Product of the exterior column variables contributed by direct ring edges. -/
noncomputable def directProduct {k m c : ℕ} {R : Type*} [CommSemiring R]
    (occ : Fin m → Fin k × Fin c × Bool) (a : RingRow k m → Bool) :
    MvPolynomial (Exterior k m c) R :=
  ∏ u, if (markedPort occ u (a u)).isSome then 1 else X (.inl (ringTarget u (a u)))

end PermanentReduction

end VPVNP
end Computability
end OAI

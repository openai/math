import OAI.Computability.VPVNP.WireTensor

/-!
# Integral coefficients of wire networks

The supply and demand networks in the motif identities of Section 6 use the
same bases over every field. Their coefficients are obtained from the integer
network by the canonical ring homomorphism.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace WireTensor

variable (R : Type*) [CommRing R] {E J : Type*} [Fintype E]
variable (a b : E → J) (I : E → Type*) [∀ e, Fintype (I e)]

/-- The equality check at each edge has integral coefficients in every characteristic. -/
theorem intCast_wireNetwork_coeff (x : ∀ j, (wireNetwork (k := ℤ) a b I).Basis j) :
    ((wireNetwork (k := ℤ) a b I).coeff x : R) = (wireNetwork (k := R) a b I).coeff x := by
  classical
  simp [wireNetwork, apply_ite Int.cast]

/-- Entrywise scalar extension of the integer network gives the network over the new ring. -/
theorem intCast_wireNetwork_coeff_fun :
    (fun x ↦ ((wireNetwork (k := ℤ) a b I).coeff x : R)) = (wireNetwork (k := R) a b I).coeff :=
  funext (intCast_wireNetwork_coeff R a b I)

end WireTensor

end VPVNP
end Computability
end OAI

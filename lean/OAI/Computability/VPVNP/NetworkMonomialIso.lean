import OAI.Computability.VPVNP.NetworkMonomials
import OAI.Computability.VPVNP.NetworkHalfIso

/-!
# Reindexing local kernel witnesses

The coordinate change on the input and output of a tensor substitution
transports the arguments of each local map. Its successful checks, choices
and parameter exponents remain the ones attached to the original map.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace NetworkKernel

variable {A : Type*} [CommRing A] {Label : Type} [Fintype Label] {κ : Label → A}
variable {N M P : Network}

/-- Transport witnesses for every local kernel entry of one placed term. -/
noncomputable def Term.reindexWitness (t : Term A N)
    (W : ∀ v a z, MonomialWitness κ (t.kernel v a z))
    (input : N.Iso M) (output : t.output.Iso P) :
    ∀ v a z, MonomialWitness κ ((t.reindex input output).kernel v a z) := by
  dsimp only [Term.reindex]
  refine (Equiv.piCongrLeft _ output.site) ?_
  intro v a z
  rw [Equiv.piCongrLeft_apply_apply]
  exact W v _ _

/-- A step written in new input coordinates carries the same finite
witnesses for every selected output term and local kernel. -/
noncomputable def Step.reindexInputWitness (s : Step A N) (input : N.Iso M)
    (W : ∀ i v a z, MonomialWitness κ ((s.term i).kernel v a z)) :
    ∀ i v a z, MonomialWitness κ (((s.reindexInput input).term i).kernel v a z) :=
  fun i ↦ (s.term i).reindexWitness (W i) input (Network.Iso.refl _)

end NetworkKernel

end VPVNP
end Computability
end OAI

import OAI.Computability.VPVNP.NetworkHalfIso

/-!
# Local factors after relabelling a network

Reindex each whole local factor by the new site and pull its incoming and
outgoing arguments back along the alphabet bijections. This preserves the
contraction, even for a network with parallel edges.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace NetworkKernel.Network.Iso

open WireTensor

variable {N M : NetworkKernel.Network}

/-- Move an arbitrary local factor to its corresponding relabelled site. -/
def pushFactors {k : Type*} (f : N.Iso M) (F : Factors k N) : Factors k M :=
  Equiv.piCongrLeft (fun u ↦ M.Half u → k) f.site fun u z ↦ F u (f.pullHalf u z)

@[simp] theorem pushFactors_at {k : Type*} (f : N.Iso M) (F : Factors k N) (u : N.Site)
    (z : M.Half (f.site u)) : f.pushFactors F (f.site u) z = F u (f.pullHalf u z) := by
  rw [pushFactors, Equiv.piCongrLeft_apply_apply]

/-- One shared payload per relabelled edge corresponds to one per original
edge. Every local factor then sees exactly its original incident arguments. -/
theorem contract_pushFactors {k : Type*} [CommSemiring k] (f : N.Iso M) (F : Factors k N) :
    contract M (f.pushFactors F) = contract N F := by
  classical
  rw [contract_edgeSum, contract_edgeSum]
  symm
  apply Fintype.sum_equiv (f.edge.piCongr f.payload)
  intro z
  apply Fintype.prod_equiv f.site
  intro u
  rw [pushFactors_at]
  simp only [pullHalf, edgeAssignment, Equiv.piCongr_apply_apply, Equiv.symm_apply_apply]

/-- Transport the finite family of individual choices counted by a local
factor. At the image site, its elements are the choices on the pulled-back
half-wire data. -/
@[instance_reducible] def pushChoiceFintype (f : N.Iso M) (P : Factors Type N)
    (fin : ∀ u z, Fintype (P u z)) : ∀ v z, Fintype (f.pushFactors P v z) :=
  Equiv.piCongrLeft (fun v ↦ ∀ z, Fintype (f.pushFactors P v z)) f.site fun u z ↦
    (f.pushFactors_at P u z).symm ▸ fin u (f.pullHalf u z)

/-- The multiplicities of the transported local choice types have the same
contraction as the original local choice counts. -/
theorem contract_pushChoiceCount (f : N.Iso M) (P : Factors Type N)
    (fin : ∀ u z, Fintype (P u z)) :
    contract M (fun v z ↦ @Fintype.card _ (f.pushChoiceFintype P fin v z)) =
      contract N (fun u z ↦ @Fintype.card _ (fin u z)) := by
  rw [← f.contract_pushFactors (fun u z ↦ @Fintype.card _ (fin u z))]
  congr 1
  funext v z
  obtain ⟨u, rfl⟩ := f.site.surjective v
  rw [f.pushFactors_at (fun u z ↦ @Fintype.card _ (fin u z)) u z]
  exact @Fintype.card_congr _ _ (f.pushChoiceFintype P fin _ z) (fin u (f.pullHalf u z))
    (Equiv.cast (f.pushFactors_at P u z))

end NetworkKernel.Network.Iso

end VPVNP
end Computability
end OAI

import OAI.Computability.VPVNP.BitSlotIndex
import OAI.Computability.VPVNP.SlotTranslation
import OAI.Computability.VPVNP.SurvivingSlots

/-!
# Integer keys for the unweighted shrinking slots

Appendix C numbers surviving slots using their motif ID, surviving type
and subdivision. A lane-zero motif is recovered from the base and tag of
the original CD wire, its old outgoing slot, its color bits and its slot
coordinate. Packing these fields into integers gives an explicit order
with no dependence on widths, maps, or the unconsumed lane length.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression.PackingData

open SurvivingSlots

variable {V H Tag L : Type*} {d c N J : ℕ}
variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable (P : PackingData V H Tag L d c)

/-- Mixed-radix index of the source coordinates of the original CD wire,
suppressing its remaining lane, which is zero in a base representative. -/
def baseMotifIndex (vertices : V ≃ Fin N) (tags : Tag ≃ Fin J) (m : P.BaseMotif) :
    Fin (N * (J * (d * (2 ^ c * d)))) :=
  let a := m.1.1
  finProdFinEquiv (vertices a.1.1.1, finProdFinEquiv (tags a.1.1.2.1,
    finProdFinEquiv (a.1.2, finProdFinEquiv (bitWordFinEquiv c a.2.1, P.slotLabel a.2.2))))

theorem baseMotifIndex_injective (vertices : V ≃ Fin N) (tags : Tag ≃ Fin J) :
    Function.Injective (P.baseMotifIndex vertices tags) := by
  rintro ⟨⟨⟨⟨⟨x, j, g⟩, i⟩, u, h⟩, hm⟩, hg⟩ ⟨⟨⟨⟨⟨x', j', g'⟩, i'⟩, u', h'⟩, hm'⟩, hg'⟩ eqn
  change g = 0 at hg
  change g' = 0 at hg'
  subst g
  subst g'
  simp only [baseMotifIndex, EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq] at eqn
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := eqn
  rfl

/-- Mixed-radix integer key for a role edge. Subdivision indices use the
sum of all four subdivision counts as their common radix. -/
def slotIdentifier (vertices : V ≃ Fin N) (tags : Tag ≃ Fin J) (subdiv : Fin 4 → ℕ)
    (i : Id P.BaseMotif subdiv) :
    Fin (4 * ((N * (J * (d * (2 ^ c * d)))) * ∑ t, subdiv t)) :=
  let bound : subdiv i.1 ≤ ∑ t, subdiv t :=
    Finset.single_le_sum (fun t _ ↦ Nat.zero_le (subdiv t)) (Finset.mem_univ _)
  finProdFinEquiv (i.1, finProdFinEquiv
    (P.baseMotifIndex vertices tags i.2.1, Fin.castLE bound i.2.2))

theorem slotIdentifier_injective (vertices : V ≃ Fin N) (tags : Tag ≃ Fin J) (subdiv : Fin 4 → ℕ) :
    Function.Injective (P.slotIdentifier vertices tags subdiv) := by
  rintro ⟨t, m, i⟩ ⟨t', m', i'⟩ h
  simp only [slotIdentifier, EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq] at h
  obtain ⟨rfl, hm, hi⟩ := h
  obtain rfl := P.baseMotifIndex_injective vertices tags hm
  have hidx : i = i' := Fin.ext (congrArg (fun j : Fin (∑ t, subdiv t) ↦ j.val) hi)
  subst i'
  rfl

/-- Sorting the lane-zero IDs is ordinary integer sorting of their keys. -/
@[instance_reducible]
def slotIdentifierOrder (vertices : V ≃ Fin N) (tags : Tag ≃ Fin J) (subdiv : Fin 4 → ℕ) :
    LinearOrder (Id P.BaseMotif subdiv) :=
  LinearOrder.lift' _ (P.slotIdentifier_injective vertices tags subdiv)

end Compression.PackingData

end VPVNP
end Computability
end OAI

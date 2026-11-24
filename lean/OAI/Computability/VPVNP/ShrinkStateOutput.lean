import OAI.Computability.VPVNP.ShrinkStateInput
import OAI.Computability.VPVNP.ShrinkSupplyReadout

/-!
# The output state of a selected shrinking layout

The surviving output is already a directed regular lift over the old base
and the tag field. Its subdivisions supply the widths of the new numbered
arcs, including the zero widths on cyclic padding arcs.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression.State

open PackingData SurvivingSlots ShrinkEnergy

variable {a b g pad : ℕ} (X : State a (packingLaneBits a g))
variable (layout : Bool) (subdiv : Fin 4 → ℕ)
variable (width : X.packingData.Motif → Fin 4 → ℕ)
variable {next : Equiv.Perm (X.Base × BitWord (packingTagBits (2 ^ a)))}
variable (I : X.packingData.ShrinkIndex layout subdiv next (2 ^ b) pad)

/-- The tag becomes part of the base, and only the unconsumed binary lane
field participates in the next lift. -/
noncomputable def shrinkOutputState : State b g where
  Base := X.Base × BitWord (packingTagBits (2 ^ a))
  baseFintype := inferInstance
  baseNonempty := inferInstance
  baseIndex := productIndex X.baseIndex (bitWordFinEquiv (packingTagBits (2 ^ a)))
  slots := I.graph
  width := X.packingData.shrinkSlotWidth layout subdiv width I.outgoing

/-- The output used by the local matrices is exactly the next state's network. -/
theorem shrinkOutputState_network :
    (X.shrinkOutputState layout subdiv width I).network =
      X.packingData.shrinkOutput layout subdiv width I := rfl

/-- Every list of motif choices packs the input sites by the same factor K. -/
theorem shrinkOutputState_positions :
    X.positions = (2 ^ (2 * 2 ^ a + 1) * 2 ^ a) *
      (X.shrinkOutputState layout subdiv width I).positions := by
  refine (packing_position_count X.Base a g).trans ?_
  congr 1
  exact Fintype.card_congr (Equiv.prodAssoc _ _ _).symm

/-- The energy on genuine motif slots equals the full state energy, since
the zero-width padding has zero charge. -/
theorem shrinkOutputState_energy :
    (X.shrinkOutputState layout subdiv width I).energy =
      ∑ i : Id X.packingData.Motif subdiv,
        (splitWidth (width i.2.1 i.1) (subdiv i.1) i.2.2 : ℝ) ^ 2 /
          equalArcMass (Site X.Base (BitWord (packingTagBits (2 ^ a))) (BitWord g)) (2 ^ b) := by
  let Y := X.shrinkOutputState layout subdiv width I
  have hpos : Y.positions =
      Fintype.card (Site X.Base (BitWord (packingTagBits (2 ^ a))) (BitWord g)) :=
    Fintype.card_congr (Equiv.prodAssoc _ _ _)
  let p := equalArcMass (Site X.Base (BitWord (packingTagBits (2 ^ a))) (BitWord g)) (2 ^ b)
  let charge (n : ℕ) := (n : ℝ) ^ 2 / p
  let e : ((Y.Base × Fin (2 ^ b)) × BitWord g) ≃ (Y.Base × BitWord g) × Fin (2 ^ b) :=
    { toFun := fun p ↦ ((p.1.1, p.2), p.1.2)
      invFun := fun p ↦ ((p.1.1, p.2), p.1.2)
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  change (∑ e, (Y.width e : ℝ) ^ 2 / (1 / ((Y.positions : ℝ) * (2 ^ b : ℕ)))) = _
  rw [hpos]
  change (∑ e, charge (Y.width e)) = _
  rw [← e.symm.sum_comp (fun e ↦ charge (Y.width e))]
  exact X.packingData.sum_shrinkSlotWidth layout subdiv width I.outgoing
    charge (by simp [charge])

end Compression.State

end VPVNP
end Computability
end OAI

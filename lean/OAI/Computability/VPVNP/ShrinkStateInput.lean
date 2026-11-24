import OAI.Computability.VPVNP.CompressionState
import OAI.Computability.VPVNP.NetworkHalfIso
import OAI.Computability.VPVNP.SlotDemandKernel
import OAI.Computability.VPVNP.ShrinkEnergy

/-!
# Reindexing the actual input of a shrinking pass

The state network numbers an outgoing edge by a full site and a slot.
Appendix C writes the same edge in color, slot-label, tag and remaining-lane
coordinates. The following relabelling identifies both incident sites and
the entire payload of each directed edge, including parallel edges.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression

open NetworkKernel

/-- Reassemble all lane fields of a packed input position. -/
def packingInputSites (V : Type) (a g : ℕ) :
    Position V (BitWord a) (BitWord (packingTagBits (2 ^ a))) (BitWord g) (2 * 2 ^ a + 1) ≃
      V × BitWord (packingLaneBits a g) where
  toFun p := (p.1.1, (packingFields a g).symm (p.2.1, p.2.2, p.1.2))
  invFun p :=
    let f := packingFields a g p.2
    ((p.1, f.2.2), f.1, f.2.1)
  left_inv := by rintro ⟨⟨v,j,l⟩,w,h⟩; simp
  right_inv := by rintro ⟨v,l⟩; simp

/-- Reassemble the outgoing edge in the original state network's site-first
numbering. The local slot index is retained at both ends. -/
def packingInputEdges (V : Type) (a g : ℕ) :
    Arc V (BitWord a) (BitWord (packingTagBits (2 ^ a))) (BitWord g) (2 ^ a) (2 * 2 ^ a + 1) ≃
      (V × BitWord (packingLaneBits a g)) × Fin (2 ^ a) where
  toFun e := (packingInputSites V a g (sourcePosition e), e.1.2)
  invFun e := packingArcEquiv V a g ((e.1.1, e.2), e.1.2)
  left_inv := by rintro ⟨⟨⟨v,j,l⟩,i⟩,w,h⟩; simp [packingInputSites, sourcePosition, packingArcEquiv]
  right_inv := by rintro ⟨⟨v,l⟩,i⟩; simp [packingInputSites, sourcePosition, packingArcEquiv]

namespace State

variable {a g : ℕ} (X : State a (packingLaneBits a g))

/-- Color and tag the base vertices in their stored numerical order. -/
abbrev packingData := orderedDyadicPacking X.slots X.baseIndex

/-- Old widths in the field order of the shrinking construction. -/
abbrev packingWidth :=
  X.width ∘ (packingArcEquiv X.Base a g).symm

/-- An isomorphism of the old wire tensor in the proof with the tensor of the
input state. On each word alphabet it is the identity. -/
noncomputable def packingInputIso :
    (X.packingData.oldWireNetwork X.packingWidth).Iso X.network where
  site := packingInputSites X.Base a g
  edge := packingInputEdges X.Base a g
  src _ := rfl
  dst e := by
    change Arc X.Base (BitWord a) (BitWord (packingTagBits (2 ^ a))) (BitWord g)
      (2 ^ a) (2 * 2 ^ a + 1) at e
    let A := packingArcEquiv X.Base a g
    have h := congrArg A.symm (orderedDyadicPacking_actual X.slots X.baseIndex (A.symm e))
    change A.symm (X.packingData.actual (A (A.symm e))) =
      A.symm (A (X.slots.actualTarget (A.symm e))) at h
    rw [A.apply_symm_apply, A.symm_apply_apply] at h
    change ((A.symm (X.packingData.actual e)).1.1,
      (A.symm (X.packingData.actual e)).2) = _
    rw [h]
    rfl
  payload _ := Equiv.refl _

/-- The independent incoming and outgoing half-words at each state site
correspond to the packed half-words at its preimage. -/
noncomputable def packingHalfEquiv
    (p : (X.packingData.oldWireNetwork X.packingWidth).Site) :=
  X.packingInputIso.pullHalfEquiv p

/-- Transport an entire packed identity, including its local kernels, to the
actual input coordinates. Every output keeps its original numbering. -/
noncomputable def reindexPackingStep {R : Type*} [CommSemiring R]
    (s : Step R (X.packingData.oldWireNetwork X.packingWidth)) :
    Step R X.network :=
  s.reindexInput X.packingInputIso

/-- Packing the input coordinates preserves the count of processor sites. -/
theorem positions_packing :
    X.positions = Fintype.card (Position X.Base (BitWord a) (BitWord (packingTagBits (2 ^ a)))
      (BitWord g) (2 * 2 ^ a + 1)) :=
  (Fintype.card_congr (packingInputSites X.Base a g)).symm

/-- The old sum in the shrinking estimate is exactly the input state's energy. -/
theorem energy_packingWidth :
    X.energy = ∑ e, (X.packingWidth e : ℝ) ^ 2 /
      ShrinkEnergy.equalArcMass (Position X.Base (BitWord a) (BitWord (packingTagBits (2 ^ a)))
        (BitWord g) (2 * 2 ^ a + 1)) (2 ^ a) := by
  unfold energy ShrinkEnergy.equalArcMass
  rw [X.positions_packing]
  apply Fintype.sum_equiv (packingArcEquiv X.Base a g)
  intro e
  simp [packingWidth]

end State
end Compression

end VPVNP
end Computability
end OAI

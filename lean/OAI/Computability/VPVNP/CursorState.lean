import OAI.Computability.VPVNP.CursorLanes
import OAI.Computability.VPVNP.CursorPaddingWidths
import OAI.Computability.VPVNP.CompressionState
import OAI.Computability.VPVNP.NetworkHalfIso

/-!
# The initial state of the compressor

Reindex the physical padded cursor network as the dyadic-degree state of
Section 7. The site map selects the designated address bits as lanes. The
edge map preserves the original parallel-arc index. The payload bijection
concatenates the fields reserved for the individual mask systems.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CursorNetwork

open CursorRouting NetworkKernel
open Compression (BitWord State)

variable {D b l a p m : ℕ} {S : Type} [Fintype S]
variable (labels : Fin D ≃ Fin b ⊕ Fin l) (hD : 1 < D) (hd : 2 + p = 2 ^ a)

/-- Padded physical arc IDs in the compressor's site-first numbering. -/
def stateEdges : PaddedArc D p ≃ ((Fin D × BitWord b) × BitWord l) × Fin (2 ^ a) :=
  (paddedEdgeEquiv D p).trans ((lanePositions labels).prodCongr (finCongr hd))

/-- Actual width on one outgoing slot at one source lane, as indexed by a state. -/
def stateWidth (bits : S → ℕ) (e : ((Fin D × BitWord b) × Fin (2 ^ a)) × BitWord l) : ℕ :=
  paddedWidth bits ((stateEdges labels hd).symm ((e.1.1,e.2),e.1.2))

/-- The Section 12 state with degree and designated lane count as indices. -/
noncomputable def cursorState (bits : S → ℕ) : State a l where
  Base := Fin D × BitWord b
  baseFintype := inferInstance
  baseNonempty := ⟨⟨⟨0, by omega⟩,0⟩⟩
  baseIndex := State.productIndex (Equiv.refl (Fin D)) (Compression.bitWordFinEquiv b)
  slots := laneGraph labels (slotSide ∘ (finCongr hd).symm) hD
  width := stateWidth labels hd bits

/-- Match the tensor network of the original cursor validators with the
input network of a typed compressor execution. -/
noncomputable def cursorStateIso (order : S ≃ Fin m) (bits : S → ℕ) :
    (paddedNetwork D p bits).Iso (cursorState labels hD hd bits).network where
  site := lanePositions labels
  edge := stateEdges labels hd
  src e := congrArg (lanePositions labels) (paddedEdge_source bits e)
  dst e := by
    let v := (paddedEdgeEquiv D p e).1
    let i := (paddedEdgeEquiv D p e).2
    have h := laneGraph_target labels (slotSide ∘ (finCongr hd).symm) hD v.1 v.2 (finCongr hd i)
    have ht := congrArg Prod.fst (paddedEdge_target hD bits e)
    change head (v.1, v.2, slotSide i) = (paddedNetwork D p bits).dst e at ht
    have h' := congrArg Prod.fst h
    simp only [Function.comp_apply, Equiv.symm_apply_apply] at h'
    exact (congrArg (lanePositions labels) ht.symm).trans h'.symm
  payload e := by
    let z := stateEdges labels hd e
    change (paddedNetwork D p bits).Payload e ≃
      (Fin (stateWidth labels hd bits ((z.1.1,z.2),z.1.2)) → Bool)
    have hw : stateWidth labels hd bits ((z.1.1,z.2),z.1.2) = paddedWidth bits e := by
      change paddedWidth bits ((stateEdges labels hd).symm (stateEdges labels hd e)) = _
      exact congrArg (paddedWidth bits) ((stateEdges labels hd).symm_apply_apply e)
    exact (paddedPayloadEquiv order bits e).trans ((finCongr hw.symm).arrowCongr (Equiv.refl _))

/-- The state position count still includes every processor and every cursor. -/
theorem cursorState_positions (bits : S → ℕ) :
    (cursorState labels hD hd bits).positions = 2 ^ D * D := by
  change Fintype.card ((Fin D × BitWord b) × BitWord l) = _
  rw [← Fintype.card_congr (lanePositions labels)]
  simp [Site, Nat.mul_comm D]

/-- The energy charged to the initial state is the energy of the actual
physical fields and all of its zero-width padding. -/
theorem cursorState_energy (bits : S → ℕ) :
    (cursorState labels hD hd bits).energy =
      ∑ e : PaddedArc D p, (paddedWidth bits e : ℝ) ^ 2 /
        (1 / (((2 ^ D * D : ℕ) : ℝ) * (2 + p : ℕ))) := by
  let coords : (((Fin D × BitWord b) × BitWord l) × Fin (2^a)) ≃
      ((Fin D × BitWord b) × Fin (2^a)) × BitWord l :=
    ⟨fun e ↦ ((e.1.1,e.2),e.1.2), fun e ↦ ((e.1.1,e.2),e.1.2), fun _ ↦ rfl, fun _ ↦ rfl⟩
  unfold State.energy
  rw [cursorState_positions, hd]
  symm
  apply Fintype.sum_equiv ((stateEdges labels hd).trans coords)
  intro e
  change _ = (paddedWidth bits ((stateEdges labels hd).symm ((stateEdges labels hd) e)) : ℝ) ^ 2 / _
  rw [Equiv.symm_apply_apply]

/-- Initial square-root energy at the state's normalized arc mass. -/
theorem cursorState_sqrtEnergy_le (bits : S → ℕ) :
    Real.sqrt (cursorState labels hD hd bits).energy ≤
      ((2 ^ D * D : ℕ) : ℝ) * (2 + p : ℕ) * (∑ s, bits s : ℕ) := by
  rw [cursorState_energy]
  exact padded_sqrtEnergy_le D p bits

end CursorNetwork

end VPVNP
end Computability
end OAI

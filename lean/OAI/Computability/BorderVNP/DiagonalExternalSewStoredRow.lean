import OAI.Computability.BorderVNP.DiagonalExternalSewFieldImage

/-! # Stored endpoint rows of the sewn and grouped layout

Each occupied exterior interval has the same global ordinal in the appended
arithmetic directory and in the exported Boolean field table. The decoded
team and block are the low endpoint, and the live row's partner and remote
block are the high endpoint of that very cable.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew.FieldExport

open Crossing
open scoped Classical

variable (p : Params) (hp : p.Valid) {E : Type*} {old : ℕ} (previous : E ↪ Fin old)

/-- The new cable ID in the physical scan is the same global ordinal used
by the arithmetic four-slot reader after the old reserved rectangle. -/
theorem merged_pieceOrdinal (c : p.Wires) :
    mergedEdges p hp previous (.inr c) =
      FourSlot.pieceOrdinal old p.sites hp.block hp.small
        (show p.literal+p.R*p.link ≤ 2*p.literal+p.R*p.link by omega) hp.room c := rfl

/-- Splitting the global physical ID selects the appended field at the
real cable's local directory ordinal. -/
theorem merged_pieceSlot (c : p.Wires) :
    finSumFinEquiv.symm (mergedEdges p hp previous (.inr c)) = Sum.inr (p.ordinal hp c) :=
  finSumFinEquiv.symm_apply_apply (Sum.inr (p.ordinal hp c) : Fin old ⊕ Fin p.slots)

/-- Arithmetic decoding of the global ID agrees with the physical low team,
its site block, and the two selected probes. -/
theorem merged_pieceDecode (c : p.Wires) :
    let idx := (mergedEdges p hp previous (.inr c)).val-old
    idx/4/p.sites = c.1.1.val.1.val ∧ idx/4%p.sites = c.2.val.1 ∧
      idx%4/2 = (FourSlot.rightProbe c).toNat ∧ idx%4%2 = (FourSlot.nextBlock c).toNat :=
  FourSlot.appendedSlot_decode old _ _ _ _

/-- The Boolean row at the cable's true ID, including the decoded remote
partner block and the physical first offset inside the shared field. -/
theorem Params.record_ordinal (c : p.Wires) :
    p.record (p.ordinal hp c) =
      ⟨true,c.1.2.val,(fieldRank c.1.1 false).val,c.1.1.val.2.val,c.2.val.2,
        (pieceBounds _ _ c).1,cableWidth c⟩ := by
  have key : p.key (p.ordinal hp c) = FourSlot.index p.sites hp.block (by omega) hp.room c :=
    (FourSlot.slotOrdinal _ _).symm_apply_apply _
  unfold Params.record
  rw [key]
  exact FourSlot.row_index c hp.block hp.small (by omega)

/-- Every unoccupied exterior directory row has canonical zero pointers and
width, even if its arithmetic probe computes nonzero candidate fields. -/
theorem Params.empty_fields (name : ℕ → ℕ → ℕ) (j : Fin p.slots)
    (unused : j ∉ Set.range (p.ordinal hp)) :
    (p.record j).live = false ∧ p.pointer name j false = 0 ∧
      p.pointer name j true = 0 ∧ p.width j = 0 := by
  have live : (p.record j).live = false := by
    cases h : (p.record j).live with
    | false => rfl
    | true =>
      obtain ⟨c,hc⟩ := (FourSlot.row_live_iff hp.block hp.small (by omega) hp.room (p.key j)).mp h
      exact False.elim (unused ⟨c,(FourSlot.slotOrdinal _ _).symm.injective
        (((FourSlot.slotOrdinal _ _).symm_apply_apply _).trans hc)⟩)
  simp [live,Params.pointer,Params.width]

variable {D : ℕ} {P : Type} {N : Network D P (fun _ => 1)}
    {phys : PublicPort p.R p.processors p.literal p.link ≃ P} (h : BlockHosts N phys p.g)

/-- The decoded source and destination addresses name the two actual retained
hosts in the grouped network, and the stored width is its physical cable width. -/
theorem endpoint_fields (c : p.Wires) :
    let j := p.ordinal hp c
    let row := p.record j
    ∃ partner : Fin (p.R+1), partner.val = row.partner ∧
      (finalLayout p h).src (.inr c) = h.host ((p.key j).1,(p.key j).2.1.val) ∧
      (finalLayout p h).dst (.inr c) = h.host (partner,row.remote) ∧
      (finalLayout p h).width (.inr c) = p.width j := by
  let j := p.ordinal hp c
  have key : p.key j = FourSlot.index p.sites hp.block (by omega) hp.room c :=
    (FourSlot.slotOrdinal _ _).symm_apply_apply _
  dsimp only
  refine ⟨c.1.1.val.2,?_,?_,?_,?_⟩
  · exact (congrArg FourSlot.Row.partner (p.record_ordinal hp c)).symm
  · rw [show p.key (p.ordinal hp c) = _ from key]
    rfl
  · exact congrArg (fun row : FourSlot.Row => h.host (c.1.1.val.2,row.remote)) (p.record_ordinal hp c).symm
  · exact (p.ordinal_fields hp (fun _ _ => 0) c).2.2.symm

end Diagonal.ExternalSew.FieldExport

end BorderVNP
end Computability
end OAI

import OAI.Computability.BorderVNP.DiagonalExternalFragmentPadding
import OAI.Computability.BorderVNP.DiagonalExternalFragmentBoundaryRead
import OAI.Computability.BorderVNP.PackedInheritedMergedEnds

/-! # The true supplied bits indexed by the numeric fragment operands -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew.Fragments

open Crossing Packing Packing.CellAddresses Packing.Inherited Cube.Physical
open private supplied_at delivered from OAI.Computability.BorderVNP.PackedInheritedMergedEnds
open private ordinal_val from OAI.Computability.BorderVNP.DiagonalExternalFragmentCables
open scoped Classical

variable {D C m n : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
    (cell : N.Site → Fin C) (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin n)
    (ports : Ports bits) (ends : Bool → LiveBit N cell → Bool)

/-- The total numeric reader used by the fragment producer agrees with the
typed final-cell operand on its actual cell and slot range. -/
noncomputable def endData (c k : ℕ) : Bool :=
  if hc : c<C then
    let v : Fin C := ⟨c,hc⟩
    if hk : k<suppliedSize N cell v then Placement.endSupply N cell v edgeID portID ports ends ⟨k,hk⟩ else false
  else false

theorem endData_at (c : Fin C) (k : Fin (suppliedSize N cell c)) :
    endData N cell edgeID portID ports ends c.val k.val = Placement.endSupply N cell c edgeID portID ports ends k := by
  simp [endData,c.isLt,k.isLt]

/-- The canonical endpoint value may differ at the two ends of a crossing. -/
theorem endData_endpoint (side : Bool) (e : N.CrossingEdge cell) (j : Fin (N.width e.val)) :
    endData N cell edgeID portID ports ends (endpointCell N cell side e).val
      (endpointRow N cell edgeID portID side e+j.val) = ends side ⟨e,j⟩ := by
  let c := endpointCell N cell side e
  let u := endpointWord N cell c side e rfl
  have h := supplied_at N cell c edgeID portID ports ends u j
  have off := ordinal_val N cell edgeID portID c u j
  change (suppliedOrdinal N cell c edgeID portID u j).val = endpointRow N cell edgeID portID side e+j.val at off
  rw [←off,endData_at,h]
  change ends (decide (cell (N.src e.val) ≠ endpointCell N cell side e)) ⟨e,j⟩ = ends side ⟨e,j⟩
  cases side <;> simp [endpointCell,e.property]

variable {R V g : ℕ} (G : Network D (FreeBlock R V) (fun _ => g)) (atCell : G.Site → Fin C)
    (ei : G.Edge ↪ Fin m) (pi : FreeBlock R V ↪ Fin n) {lp : ℕ → ℕ × ℕ}
    (place : LivePlacement G atCell ei pi lp)

include place in
/-- The receiver slot of a grouped word is the true typed evaluator ordinal. -/
theorem placedOrdinal (c : Fin C) (p : {p : FreeBlock R V // atCell (G.attach p) = c}) (j : Fin g) :
    laneAddress lp ⟨p.val,j⟩ = (c.val,(suppliedOrdinal G atCell c ei pi (.inr p) j).val) := by
  rcases p with ⟨p,h⟩
  subst c
  change ((lp _).1,(lp _).2+j.val) = _
  rw [place p]
  exact Prod.ext rfl (ordinal_val G atCell ei pi (atCell (G.attach p)) (.inr ⟨p,rfl⟩) j).symm

include place in
/-- The physical address of every grouped lane reads the indicated external bit. -/
theorem endData_group (input : Ports (fun _ : FreeBlock R V => g)) (routed : Bool → LiveBit G atCell → Bool)
    (a : Σ _ : FreeBlock R V, Fin g) :
    let pos := laneAddress lp a
    endData G atCell ei pi input routed pos.1 pos.2 = input a.1 a.2 := by
  rcases a with ⟨p,j⟩
  intro pos
  have addr := placedOrdinal G atCell ei pi place (atCell (G.attach p)) ⟨p,rfl⟩ j
  change endData _ _ _ _ _ _ (laneAddress lp ⟨p,j⟩).1 (laneAddress lp ⟨p,j⟩).2 = _
  rw [addr,endData_at]
  exact supplied_at G atCell (atCell (G.attach p)) ei pi input routed (.inr ⟨p,rfl⟩) j

/-- Every finite supplied index is a lane of exactly the type used by the
physical translator, independent of which finite enumeration is synthesized. -/
theorem suppliedOrdinal_surj {A : Type} (loc : N.Site → A) (c : A) (k : Fin (suppliedSize N loc c)) :
    ∃ (u : Supplied N loc c) (j : Fin (suppliedWidth N loc c u)), suppliedOrdinal N loc c edgeID portID u j = k := by
  let ord := CellSlabs.ordinal (suppliedRow N loc c edgeID portID) (suppliedWidth N loc c)
  exact ⟨(ord.symm k).1,(ord.symm k).2,ord.apply_symm_apply k⟩

end Diagonal.ExternalSew.Fragments

end BorderVNP
end Computability
end OAI

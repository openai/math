import OAI.Computability.BorderVNP.CellPacketGeometryOpaqueSlots
import OAI.Computability.BorderVNP.CellPacketGeometryHistoryTables

/-! # Reading original description addresses from the shared terminal table

The retained raw site-owner pins identify the receiving cell. The marker pins in
the shared terminal address view supply the actual cell sizes. Neither field
requires a RAM read of the completed private placement.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.History.Native.OpaqueSlots

open Crossing Packing Packing.Inherited CellAddressCircuit CellAddresses CellSparse.Packet
open ParseBatchSort VPVNP.VerifierNetwork RoutingISA

variable {J a m n C d k w : ℕ} {σ Orig : Type} [Fintype σ] (F : Fields a m n C d k w σ)

private def wire (entry : Fin J → Fin a) : Input J C k w → σ ⊕ TerminalTable.Outputs a m n C k w
  | .inl (i,j) => .inl (F.owner (entry i) j)
  | .inr (c,b,j) => .inr (.inl (.inr (.inr (if b then 2 else 1,c)),j))

/-- Pointer producer on the joint input and terminal geometry pins. A caller can
attach it to a shared terminal frame while retaining that frame's other outputs. -/
noncomputable def fromBank (entry : Fin J → Fin a) (arena stride gap desc : ℕ) :
    Frame (σ ⊕ TerminalTable.Outputs a m n C k w) (Fin J × Fin w) :=
  (frame F.cells (fun c => arena+stride*c.val+gap) desc).subst (Frame.initial (wire F entry))

variable {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
variable (cell : N.Site → Fin C) (aux : N.Site → ℕ) (siteID : N.Site ↪ Fin a) (edgeID : N.Edge ↪ Fin m)
variable (portID : P ↪ Fin n) {x : σ → Bool} (physical : CellAddressPhysical.Represents N cell aux siteID edgeID portID F x)
variable (fit : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^w)

include physical fit in
/-- Each genuine original key returns its absolute supplied-bank address at the
real retained terminal host, in the native private-placement row order. -/
theorem fromBank_live (boxes : Fin a → List (Source.Box Orig)) (entry : Fin J → Fin a) (host : Fin J → N.Site)
    (sites : ∀ i, entry i=siteID (host i)) (old : ℕ → ℕ) (owners : ∀ i, old i.val=(cell (host i)).val)
    (arena stride gap desc : ℕ) (hd : desc < 2^w)
    (room : ∀ c : Fin C, (∑ i : Fin J, if cell (host i)=c then desc else 0) < 2^w)
    (i : Fin J)
    (limit : arena+stride*(cell (host i)).val+suppliedSize N cell (cell (host i))+gap+
      PrivatePlacement.prefixCounts old desc i.val (cell (host i)).val < 2^w) :
    value (fun j => (fromBank F entry arena stride gap desc).eval ((TerminalTable.bank F boxes).withInput.eval x) (i,j)) =
      arena+stride*(cell (host i)).val+suppliedSize N cell (cell (host i))+gap+
        PrivatePlacement.prefixCounts old desc i.val (cell (host i)).val := by
  let y := (Frame.initial (wire F entry)).eval ((TerminalTable.bank F boxes).withInput.eval x)
  have actual (j : Fin J) : value (fun b => y (.inl (j,b))) = (F.cells (cell (host j))).val := by
    simpa only [y,Frame.initial_eval,wire,Frame.withInput_eval_inl,sites,Function.comp_def] using physical.owner (host j)
  have width (c : Fin C) : extent y c = suppliedSize N cell c := by
    have supply := (SuppliedOffsets.size_value F x c).symm.trans
      (SuppliedOffsets.cell_size N cell aux siteID edgeID portID F physical fit c)
    simpa only [extent,y,Frame.initial_eval,wire,Bool.true_eq,ite_true,Bool.false_eq_true,ite_false,
      Frame.withInput_eval_inr,TerminalTable.bank,parallelFrame_eval_inl] using supply
  let base := fun c : Fin C => arena+stride*c.val+gap
  have within : base (cell (host i))+extent y (cell (host i))+
      PrivatePlacement.prefixCounts old desc i.val (cell (host i)).val < 2^w := by rw [width]; dsimp [base]; omega
  have out := value_at F.cells base desc y (cell ∘ host) old owners actual hd room i within
  simp only [Function.comp_apply,base,width] at out
  rw [show arena+stride*(cell (host i)).val+suppliedSize N cell (cell (host i))+gap =
    arena+stride*(cell (host i)).val+gap+suppliedSize N cell (cell (host i)) by omega]
  simpa only [fromBank,Frame.subst_eval,y] using out

/-- Attaching the terminal pin selection costs no gates beyond the pointer frame. -/
theorem fromBank_cubic (entry : Fin J → Fin a) (arena stride gap desc R W : ℕ) (rows : C+J+1 ≤ R)
    (widths : k≤W ∧ w≤W ∧ Nat.clog 2 R≤W) :
    (fromBank F entry arena stride gap desc).size ≤ 2500*R*(W+1)^3 := by
  simpa only [fromBank,Frame.subst_size,Frame.initial_size,zero_add] using
    frame_cubic (J:=J) (w:=w) F.cells (fun c => arena+stride*c.val+gap) desc R W rows widths

end CellPacketGeometry.History.Native.OpaqueSlots

end BorderVNP
end Computability
end OAI

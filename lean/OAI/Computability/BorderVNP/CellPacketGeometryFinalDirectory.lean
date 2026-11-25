import OAI.Computability.BorderVNP.CellPacketGeometryOrderedRun
import OAI.Computability.BorderVNP.CellPacketSupplementalTyped
import OAI.Computability.BorderVNP.PackedBankSortedCell

/-! # Identifying a sorted sparse cell with its actual network directory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.SiteWords

open Crossing Shortening CellSparse CellSparse.Packet Packing Packing.Inherited RoutingISA.CellPacket

variable {s C : ℕ} {Orig A : Type}

/-- The actual per-cell task constructed from its numeric source ranges,
externals, one-copy tables, and the site-major geometry output. -/
def Directory.placed (G : Directory (Fin s) Orig C) (c : Fin C) (H : ℕ) (slot : Orig → ℕ)
    (fs : Orig → List Factor) (pub desc ext scratch burst : ℕ) (external : List Bool) : Placed Orig :=
  ⟨G.privateWires c,G.cellBoxes c,G.cellRecords c,G.reports c,slot,H,fs,pub,desc,ext,scratch,burst,external⟩

private theorem actual_table (owner : Fin s → Fin C) (c : Fin C) (xs ys : Fin s → List A)
    (cells : ∀ i, owner i = c → xs i = ys i) :
    (owned c owner (List.finRange s)).flatMap xs = BankBoxOrdinal.table (fun i => (owner i).val) ys c.val := by
  rw [BankBoxOrdinal.table_eq_filtered]
  simp only [Fin.val_inj]
  apply List.flatMap_congr
  intro i hi
  exact cells i (of_decide_eq_true (List.mem_filter.mp hi).2)

variable {D n p : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
variable (cell : N.Site → ℕ) (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin n) (portID : P ↪ Fin p)
variable (state : N.Site → Site)

/-- Per-slot identification of the actually emitted tables and anchored record blocks
identifies the entire public/opaque cell directory. Empty geometry slots outside
this cell (in particular the inactive sentinel) impose no constraint. -/
theorem Directory.placed_final (G : Directory (Fin s) Orig C) (c : Fin C) (H : ℕ) (slot : Orig → ℕ)
    (fs : Orig → List Factor) (pub desc ext scratch burst : ℕ) (external : List Bool)
    (ordered : G.sites=List.finRange s)
    (tables : ∀ i, G.owner i=c → (G.boxes i).map (Source.factors fs) =
      FinalCell.slots siteID (fun v => (state v).boxes) i)
    (records : ∀ i, G.owner i=c → G.rows i = FinalCell.slots siteID
      (fun v => (state v).placedRows (CellAddresses.siteBase N cell (cell v) siteID (fun z => (state z).size) ⟨v,rfl⟩)
        (FinalCell.firstBox siteID (fun z => (G.owner z).val) state v) ++
        FinalCell.binding N cell siteID edgeID portID state v) i) :
    (G.placed c H slot fs pub desc ext scratch burst external).directory =
      FinalCell.directory (fun z => (G.owner z).val) N cell siteID edgeID portID state c.val (G.reports c) := by
  let target := FinalCell.directory (fun z => (G.owner z).val) N cell siteID edgeID portID state c.val (G.reports c)
  have bx : (G.cellBoxes c).map (Source.factors fs) = target.boxes := by
    rw [FinalCell.directory_boxes]
    simp only [Directory.cellBoxes,ordered,List.map_flatMap]
    exact actual_table G.owner c _ _ tables
  have rr : G.cellRecords c = target.records := by
    rw [FinalCell.directory_rows]
    simp only [Directory.cellRecords,ordered]
    exact actual_table G.owner c _ _ records
  change CellSparse.Directory.mk ((G.cellBoxes c).map (Source.factors fs)) (G.cellRecords c) (G.reports c) = target
  rw [bx,rr]
  rfl

end CellPacketGeometry.SiteWords

namespace RoutingISA.CellPacket.Supplement

open CellSparse
variable {Orig : Type}

/-- The actual supplemental call transports directly to the identified physical
network directory, preserving its private bank, external bits, and tail order. -/
theorem final_payload (p : Placed Orig) (D : Directory) (base : ℕ) (l : Layout) (extra : List Record)
    (physical : p.directory=D) :
    (task l p base extra).payload = Packet.input {D with records := D.records++extra} p.privateWires p.external := by
  have rr : p.rows = D.records := congrArg Directory.records physical
  rw [payload_eq,physical,rr]

end RoutingISA.CellPacket.Supplement

end BorderVNP
end Computability
end OAI

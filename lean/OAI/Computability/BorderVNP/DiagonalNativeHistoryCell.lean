import OAI.Computability.BorderVNP.DiagonalNativeOwnedCellInputs
import OAI.Computability.BorderVNP.CellPacketGeometryHistoryFinal
import OAI.Computability.BorderVNP.CellTeamReportCharge

/-! # The complete restored private cell on the physical history and incidence tapes -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.History

open Crossing Shortening CellSparse Packet Packing Packing.Inherited FrozenTape LiveWords SiteWords
open RoutingISA RoutingISA.CompactMachine RoutingISA.SparseExterior DiagonalTallyCellReports

variable {a C cap d t : ℕ} {R B U V E Orig : Type}
variable (S : Schema R B) (L : Schema U V) (boxes : Fin a → List (Source.Box Orig))
variable (sh : ∀ r, (S.tags r).length≤cap) (lh : ∀ r, (L.tags r).length≤cap)
variable (priv : Fin (C+1) → E) (rep : Fin (C+1) → List (List E)) (args : E → ℕ)
variable (x : Pins R B d → Bool) (y : Pins U V t → Bool) (cells : Fin a → Fin C) (off box : Fin a → ℕ)
local notation3 "G₀" => directory S L boxes sh lh priv rep args x y cells off box
variable {D n p : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
variable (cell : N.Site → ℕ) (siteID : N.Site ↪ Fin a) (edgeID : N.Edge ↪ Fin n) (portID : P ↪ Fin p)
variable (state : N.Site → Site)

/-- The typed original-site source, actual frozen history and binding tapes determine
the complete signed private cell on any report assignment. The reported count and
weighted-use digits come from that report itself. The record suffix is the physical
weighted-source scan's binding rows for the very same original bundles. -/
theorem logical_owned_history (c : Fin C) (places : Fin (C+1) → CellPacket.Placed Orig)
    (shape : TypedBatch.SourceShape places G₀) (fs : Orig → List Factor)
    (originalTables : (places c.castSucc).factors=fs)
    (historical : S.Image x (siteID.trans Fin.valEmbedding) state)
    (final : L.Section y (siteID.trans Fin.valEmbedding) (FinalCell.binding N cell siteID edgeID portID state))
    (table : ∀ i, (boxes i).map (Source.factors fs) = FinalCell.slots siteID (fun v => (state v).boxes) i)
    (bitBase : ∀ v, off (siteID v)=CellAddresses.siteBase N cell (cell v) siteID (fun z => (state z).size) ⟨v,rfl⟩)
    (boxBase : ∀ v, box (siteID v)=FinalCell.firstBox siteID (fun j => (cells j).val) state v)
    (reportLayout : ReportLayout) (report : ReportCell reportLayout) (cursor : LocalReportCursor)
    (privateHeader : args (priv c.castSucc)=CellAddresses.externalBase N cell c.val (fun v => (state v).size))
    (countFieldsAt : (rep c.castSucc).map (List.map args) =
      countFields (FinalCell.countBase N cell state c.val) reportLayout.gadgets reportLayout.countWidth)
    (field : SparseExterior.Field) (supply : List Bool) (restored : field.values=supply++report.bits) :
    logicalCell (places c.castSucc) (bindingRows report.bundles cursor) field =
      FinalCell.withWiring
        (FinalCell.cellInput N cell siteID edgeID portID (fun i => (cells i).val) state c.val
          reportLayout.gadgets reportLayout.countWidth (supply++report.bits))
        (bindingRows report.bundles cursor) := by
  let source := places c.castSucc
  have header : source.privateWires=FinalCell.privateBits N cell state c.val :=
    (shape.privateWires c.castSucc).trans privateHeader
  have reported : (G₀).reports c.castSucc =
      countFields (FinalCell.countBase N cell state c.val) reportLayout.gadgets reportLayout.countWidth := countFieldsAt
  have sorted := placed_directory S L boxes sh lh priv rep args x y cells off box N cell siteID edgeID portID state c
    0 (fun _ => 0) fs 0 0 0 0 0 [] historical final table bitBase boxBase
  have assembled : source.directory = ((G₀).placed c.castSucc 0 (fun _ => 0) fs 0 0 0 0 0 []).directory := by
    change CellSparse.Directory.mk (source.boxes.map (Source.factors source.factors)) source.rows source.reports =
      CellSparse.Directory.mk (((G₀).cellBoxes c.castSucc).map (Source.factors fs)) ((G₀).cellRecords c.castSucc) ((G₀).reports c.castSucc)
    simp only [source,shape.boxes,shape.records,shape.reports,originalTables]
  have physical := assembled.trans sorted
  rw [reported] at physical
  change CellInput.mk (BottomReports.appendRows source.directory _) source.privateWires field.values =
    CellInput.mk (BottomReports.appendRows _ _) _ _
  rw [physical,header,restored]
  rfl

end CellPacketGeometry.History

end BorderVNP
end Computability
end OAI

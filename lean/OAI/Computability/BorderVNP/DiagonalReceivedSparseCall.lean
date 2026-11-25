import OAI.Computability.BorderVNP.DiagonalReceivedReportExtent
import OAI.Computability.BorderVNP.PackedScheduledPlacedCall

/-! # The pre-call resource certificate on every received report proposal -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeAssignments

open Crossing Packing Packing.CellAddresses Packing.BottomReports Packing.Inherited
open Site.Programs CellSparse DiagonalTallyCellReports RoutingISA CompactMachine TeamScales

variable {T C D ns ne np : ℕ} {P J Origin : Type} [Fintype P] [Fintype J] {bits : P → ℕ} {layout : Fin T → ReportLayout}
    (R : ReceivedRows layout C) (N : Network D P bits) (cell : N.Site → Fin C)
    (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin ne) (portID : P ↪ Fin np)
    (owner : Fin ns → ℕ) (state : Site.Programs N)
    (host : J ↪ N.Site) (bundle : J → Bundle) (origins : Fin C → List J)
    {M E Z high table H coeff k B j n r w : ℕ}
    (b : ReceivedBounds R N cell siteID owner state host bundle origins M E Z high table H
      (coeff*(logWidth r n+1)^k))
    (paid : SparseExterior.PrivateCallsAt 3076 table (B+10) (j+1) H coeff k n r)
    (u : Fin T) (i : Fin (R.cells u).length)
local notation3 (prettyPrint := false) "c" => R.order ⟨u,i⟩
local notation3 (prettyPrint := false) "input" => FinalCell.cellInput N (fun v => (cell v).val) siteID edgeID portID
  owner (fun v => (state v).program) (c).val (layout u).gadgets (layout u).countWidth
local notation3 (prettyPrint := false) "cursor" => FinalCell.countBase N (fun v => (cell v).val) (fun v => (state v).program)
  (c).val + (layout u).gadgets*(layout u).countWidth

include b paid in
/-- The received cell and its actual tape length suffice for both the native
producer's burst bound and the residual private-call clock, before the individual
count digits or marked uses are validated. -/
theorem ReceivedBounds.scheduledArgument
    (hn : 1≤n) (hr : 1≤r) (hH : 9≤H) (hm : M≤TeamScales.width n (1/5)) (he : E≤TeamScales.width n (1/4))
    (hw : 0<w) (hwn : w≤n) (digits : high.size+1≤B*(logWidth r n+1)^j) (size : 3*M+Z≤4*(M+E+1)^3)
    (field : SparseExterior.Field) (sorted : SparseExterior.Ordered field.width 0 field.spans)
    (pos : ∀ s ∈ field.spans, 0<s.bits.length)
    (supplied : field.width=suppliedSize N (fun v => (cell v).val) (c).val)
    (length : field.tail.length=((R.cells u).get i).tailWidth)
    (placed : CellPacket.Placed Origin) (extra : List Record)
    (seen : SparseExterior.logicalCell placed extra field =
      FinalCell.withWiring (input field.values) (supplements cursor ((origins c).map bundle))) :
    let logical := SparseExterior.logicalCell placed extra field
    (CompactFrame.pack w (Packet.input logical.directory logical.privateWires field.bytes)).length≤TeamScales.width n (1/2) ∧
      logical.directory.ProfileWidths ∧ SparseExterior.clock w logical.directory logical.privateWires field≤n^25 := by
  obtain ⟨total,room,tail,boxes⟩ := b.fieldInputs R N cell siteID owner state host bundle origins u i field supplied length
  exact FinalCell.scheduled_placed_call (Diagonal.sparseCellBudget_of_privateCalls paid) hn hr hH hm he hw hwn
    digits size N (fun v => (cell v).val) siteID edgeID portID owner (fun v => (state v).program) (c).val
    (layout u).gadgets (layout u).countWidth field b.ownerID b.incoming b.schema (b.publicLoad c) (b.expandedLoad c)
    (b.gadgetCount u) (b.countWidth u) (b.widthBound u) sorted pos (fun v _ => b.scalars v) (fun v _ => b.rowSize v)
    b.tableSize b.split ((origins c).map bundle) total supplied tail room boxes placed extra seen

end Cube.Physical.NativeAssignments

end BorderVNP
end Computability
end OAI

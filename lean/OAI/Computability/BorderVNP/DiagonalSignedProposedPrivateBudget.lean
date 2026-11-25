import OAI.Computability.BorderVNP.DiagonalReceivedSparseCall
import OAI.Computability.BorderVNP.DiagonalPublishedSparseCell
import OAI.Computability.BorderVNP.DiagonalNativeReportBindings
import OAI.Computability.BorderVNP.CellSparseExteriorTeamCost

/-! # Funding the scanner before constructing any sparse argument row -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeAssignments

set_option maxRecDepth 7000
set_option maxHeartbeats 1000000

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

open VPVNP.BurstRAM FragmentRows Diagonal.ExternalSew.Fragments

include b paid in
/-- A proposed report already has a sparse private-call budget on the
unfiltered native fragment stream. In particular its first inequality funds
the initial compact-row constructor before a sparse exterior run exists. -/
theorem ReceivedBounds.scheduled_report_proposal
    (hn : 1≤n) (hr : 1≤r) (hH : 9≤H) (hm : M≤TeamScales.width n (1/5)) (he : E≤TeamScales.width n (1/4))
    (hw : 0<w) (hwn : w≤n) (digits : high.size+1≤B*(logWidth r n+1)^j) (size : 3*M+Z≤4*(M+E+1)^3)
    (assigned : ReportAssignments (R.cells u)) (f : FragmentRows.Layout) (ram : ℕ → ℕ)
    (data : ℕ → ℕ → Bool) (placed : CellPacket.Placed Origin) (extra : List Record)
    (supplied : ((R.cells u).get i).supplied=suppliedSize N (fun v => (cell v).val) (c).val)
    (scan : ram (f.supplied+(c).val)=((R.cells u).get i).supplied)
    (ordered : SparseExterior.Ordered (ram (f.supplied+(c).val)) 0 (spans (f.stream ram) data (c).val)) :
    let proposal := assigned.val.get (Fin.cast assigned.length.symm i)
    let field : SparseExterior.Field := ⟨proposal.supplied,spans (f.stream ram) data (c).val,proposal.bits⟩
    let logical := SparseExterior.logicalCell placed extra field
    logical=FinalCell.withWiring (input field.values) (supplements cursor ((origins c).map bundle)) →
      (CompactFrame.pack w (Packet.input logical.directory logical.privateWires field.bytes)).length≤TeamScales.width n (1/2) ∧
        logical.directory.ProfileWidths ∧ SparseExterior.clock w logical.directory logical.privateWires field≤n^25 := by
  intro proposal field logical seen
  have shape := assigned.row_eq i
  have sz := congrArg ReportCell.supplied shape
  have sizeEq : proposal.supplied=((R.cells u).get i).supplied := by
    change (assigned.val[i.val]'(i.isLt.trans_eq assigned.length.symm)).supplied=((R.cells u)[i.val]).supplied
    exact sz
  have tail : proposal.bits.length=((R.cells u).get i).tailWidth := by
    rw [ReportCell.bits_length]
    have old := congrArg ReportCell.tailWidth shape
    change (assigned.val[i.val]'(i.isLt.trans_eq assigned.length.symm)).tailWidth=((R.cells u)[i.val]).tailWidth
    simpa only [ReportCell.withTape_tailWidth] using old
  apply b.scheduledArgument R N cell siteID edgeID portID owner state host bundle origins paid u i hn hr hH hm he hw hwn digits size
    field _ _ (sizeEq.trans supplied) tail placed extra seen
  · change SparseExterior.Ordered proposal.supplied 0 (spans (f.stream ram) data (c).val)
    rwa [sizeEq,←scan]
  · exact fun span member => stream_positive _ _ _ _ _ _ span member

end Cube.Physical.NativeAssignments

end BorderVNP
end Computability
end OAI

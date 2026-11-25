import OAI.Computability.BorderVNP.DiagonalSignedReceivedFinish
import OAI.Computability.BorderVNP.CubePhysicalReportReaders

/-! # The measured native finish for a complete recovered operand table -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeLedger

open VPVNP.BurstRAM Crossing Diagonal Diagonal.CellEntries DiagonalTallyRAM DiagonalTallyAllocation
open DiagonalTallyMaterialize DiagonalTallyCellReports RoutingISA DiagonalResidueRAM
open TeamContraction.ProcessorSlots TeamContraction.JointHeader TeamContraction.JointHeader.PositiveFields
open RoutingISA.SignedTaskArena RoutingISA.Evaluator FiniteEvaluator NativeAssignments
open scoped BigOperators Classical

variable {D B w : ℕ} {P : Type} {bits : P → ℕ} {N : Network D P bits}
    (sa : SignedTaskArena.Layout) (pub : Arg → Word w) (control fieldWidth bodyCap : ℕ)
set_option quotPrecheck false
set_option autoImplicit false
local notation "layout" => reportLayout sa.before sa.after (Fin.val (pub 0)) control sa.p.parameters fieldWidth bodyCap sa.cube.stop
local notation "gadgets" => sa.p.report.gadgets
local notation "nteams" => sa.cube.teams
variable {cell : N.Site → Fin sa.cube.cells}
    (slot : LiveBit N cell ↪ Slot sa.cube.n sa.cube.header.d sa.cube.header.blocks (sa.cube.h*sa.cube.b))
    (tags : N.Tables (Entry (Fin sa.p.parameters) (Fin sa.p.report.gadgets))) (x : Ports bits)
    (id : TableEntry sa.cube.n sa.cube.b sa.cube.h sa.cube.K sa.cube.s → Fin sa.p.report.gadgets)
    (words : PowerWords (Fin sa.cube.teams) (Fin sa.p.parameters) (Fin sa.p.report.gadgets) B N tags)
    (label : Fin sa.cube.cells → Label (sa.cube.n+1) sa.cube.header.d) (team : Fin sa.cube.header.d → Fin sa.cube.teams)
    (a : Path N cell sa.cube.n sa.cube.header.d sa.cube.header.blocks sa.cube.b sa.cube.h sa.cube.K sa.cube.s)
    (rc : ReceivedRows (fun _ : Fin sa.cube.teams => reportLayout sa.before sa.after (Fin.val (pub 0)) control sa.p.parameters fieldWidth bodyCap sa.cube.stop) sa.cube.cells)
    (hosts : ∀ j : (u : Fin sa.cube.teams) × Fin (rc.cells u).length, pathCellOwner label team a (rc.order j)=j.1)
    (t : Fin sa.cube.teams) (tapes : ∀ u : Fin sa.cube.teams, ReportTape (rc.cells u))
    (packets : Packet sa.cube.n sa.cube.header.d sa.cube.header.blocks × Vertex (sa.cube.n+1) → PacketRead)

local notation "stream" => fun (u : Fin nteams) (j : ℕ) => if h : j<(reportBits (rc.cells u)).length then tapes u ⟨j,h⟩ else false
local notation "reports" => rc.reportedWithTape stream (fun _ => 0)
local notation "order" => rc.ledgerOrder tags words label team a hosts t
local notation "ordering" => Orders.withNativeVertices tags words label team a t order
local notation "tablePosition" => fun (_ : Packet sa.cube.n sa.cube.header.d sa.cube.header.blocks) => id
local notation "rows" => physicalRow slot tags x tablePosition words label team a
local notation "cs" => teamReports tags words label team a t ordering reports
local notation "cursor" => sa.after.reportCursor
local notation "data" => pathBanks a sa.cube.header.packetBase sa.cube.singleBank
local notation "X" => gadgetLookup sa pub (Fin.val ∘ team) t.val D data

variable {reserve axes groups cap width : ℕ} (A : StartupArena)
    (p : PositiveFields reserve axes groups cap sa.cube.teams sa.dim width)
local notation "raw" => rawAddress A reserve axes groups cap

include packets

set_option synthInstance.maxSize 4000
set_option maxRecDepth 14000
set_option maxHeartbeats 1800000

/-- Interpret the selected team's recovered original operand readers in the
actual signed program. The resulting receipt contains the protected memory,
the individual operand lookup events and their true transition bound. -/
theorem receivedFinishFromReads {banks : CellBanks.Layout} (mac : TeamOpcode.Macros w 8) {s : Bank w} {m : Memory w}
    (V : SignedPrep.Visits sa.id pub mac s m) {description : ℕ}
    (seed : PreparedReportInput pub V.controls.val.2.2 (rc.cells t) cursor description)
    (tape : tapes t=(reportReturnEquiv seed mac V.controls.val.2.1).symm V.reports)
    (alloc : ReportAllocation sa.before sa.after banks layout (rc.cells t) cursor)
    (bankStart : banks.bankStart=sa.cube.cellBank) (bankCount : banks.cells=sa.cube.cells)
    (bankStride : banks.stride=sa.cube.cellStride) (frame : (pub 0).val=A.frame)
    (parsed : HeaderSeed sa p pub raw t.val V.arguments.val.2.2)
    (deck : CubePacket.WordPrepared X sa.id pub V.owned.val.2.2)
    (H : OpenSuffix.Inputs) (openPlace : OpenSuffix.Placement H sa.cube sa.before (pub 0).val (readings V.owned.val.2.2))
    (openReady : OpenSuffix.Ready H (pub 0).val (readings V.owned.val.2.2) w)
    (wpos : 0<w) (reportDim : sa.dim≤2^w) (reportWidth : (layout).countWidth≤w)
    (marks : ∀ c∈rc.cells t, ∀ b∈c.bundles, ∀ g∈b.positions, g.parameter<2^w ∧ g.place<w)
    (offsets ctl live ports : ℕ)
    (sortedLo : (pub 0).val+112≤ sa.p.sorted) (sortedHi : sa.p.sorted+sa.p.padded≤ sa.cube.header.packetBase)
    (ctlLo : (pub 0).val+112≤ctl) (ctlHi : ctl+37≤ sa.cube.header.packetBase)
    {u v k : ℕ} (place : sa.SparsePlacement (pub 0).val ctl)
    (fit : (FragmentRows.Layout.fromFrame (pub 0).val (readings V.reports.val.2.2)).Fits w (readings V.reports.val.2.2))
    (pointer : readings V.reports.val.2.2 ((pub 0).val+92)=ctl)
    (controls : ∀ j : Fin 37, readings V.reports.val.2.2 (ctl+j.val)=sa.controls j.val)
    (nc : (FragmentRows.Layout.fromFrame (pub 0).val (readings V.reports.val.2.2)).host.count=sa.cube.cables)
    (nr : readings V.reports.val.2.2 ((pub 0).val+9)≤ sa.cube.maxRows) (cc : readings V.reports.val.2.2 ((pub 0).val+11)=sa.cube.cells)
    {Orig : Type} (placed : ℕ → CellPacket.Placed Orig) (geom : ℕ → ℕ) (extra : ℕ → List CellSparse.Record)
    (production : let parts := (ScheduleClock.argumentVisitsEquiv pub mac V.reports.val.2.1 V.reports.val.2.2).symm V.arguments
      ∃ src : ScheduleClock.SparseCallInput pub parts.2.1.val.2.2, ScheduleClock.ProducedRoster sa
        (sa.controlRows t.val (pub 0).val offsets ctl live ports) (readings parts.1.val.2.2) placed geom extra src)
    (codes : ∀ e,sa.id e=(id e).val)
    (vertexCap : (X).frame.count≤ sa.p.report.vertices)
    (digitsFit : Tally.argumentWidth sa.cube.n sa.cube.b sa.cube.h sa.cube.K sa.cube.s≤ sa.p.report.cubeWidth)
    (headerSize : A.header=PositiveFields.width reserve axes groups cap nteams sa.dim width)
    (position : A.next≤ sa.cube.header.header) (endFit : sa.endAddress w u v k<2^w)
    (teamsFit : nteams<2^w) (widthFit : width≤w)
    (reads : ReportReaders slot tags x words label team a t ordering reports)
    (bounded : ∀ c,rows t c<2^w) :
    let state := cellBank pub mac V.arguments.val.2.1 V.arguments.val.2.2
    ∃ receipt : FinishInput t rows width pub mac state V.arguments.val.2.2 p.tallyWords,
      receipt.post=sa.after ∧ receipt.raw=raw ∧
      receipt.operands=receiptOperands tags tablePosition words label team a t ordering reports sa.after cursor
        (pub 0).val (sa.cube.stop+1) ∧
      (∀ k < sa.after.start, k ≠ (pub 0).val+35 → receipt.selected k=V.arguments.val.2.2 k) ∧
      traceCost receipt.earlier ≤ selectedOperandsTicks (X).frame.count (X).frame.width :=
  receivedFinish sa pub control fieldWidth bodyCap slot tags x id words label team a rc hosts t tapes reads.use
    reads.cells packets A p mac V seed tape alloc bankStart bankCount bankStride frame parsed deck H openPlace openReady
    wpos reportDim reportWidth marks offsets ctl live ports sortedLo sortedHi ctlLo ctlHi place fit pointer controls
    nc nr cc placed geom extra production codes vertexCap digitsFit headerSize position endFit teamsFit widthFit
    reads.useBit reads.siteID reads.source reads.align reads.fields reads.digits bounded

end Cube.Physical.NativeLedger

end BorderVNP
end Computability
end OAI

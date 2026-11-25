import OAI.Computability.BorderVNP.DiagonalSignedFinishFromReads
import OAI.Computability.BorderVNP.DiagonalJointPositiveProgram

/-! # The checked finish of an actual returning positive prefix -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeLedger

open VPVNP.BurstRAM Crossing Diagonal Diagonal.CellEntries DiagonalTallyRAM DiagonalTallyAllocation
open DiagonalTallyMaterialize DiagonalTallyCellReports RoutingISA DiagonalResidueRAM
open TeamContraction.ProcessorSlots TeamContraction.JointHeader TeamContraction.JointHeader.PositiveFields
open RoutingISA.SignedTaskArena RoutingISA.Evaluator FiniteEvaluator NativeAssignments
open scoped BigOperators Classical

open CompactMachine CellMacro.Generator

section Prefix
variable {n d b h K s w : ℕ} {id : TableEntry d b h K s → ℕ} {gen : Fragment IO}
  (S : PositiveTeam id gen n w) (pr : S.Prefix)

/-- Split the real preparation return of this prefix into its seven native visits. -/
noncomputable abbrev prefixVisits :=
  (SignedPrep.visitsEquiv id S.pub (install gen n S.routines) (S.pins pr.1).val.2.1 (S.pins pr.1).val.2.2).symm
    pr.2

/-- The argument materialization returns on precisely the register bank and RAM
recorded by the original positive preparation. -/
theorem prefixVisits_state : (prefixVisits S pr).arguments.val.2 = pr.2.val.2 := by
  let split := SignedPrep.visitsEquiv id S.pub (install gen n S.routines) (S.pins pr.1).val.2.1 (S.pins pr.1).val.2.2
  exact (SignedPrep.visitsEquiv_outState id S.pub _ (prefixVisits S pr)).symm.trans
    (congrArg (fun p => p.val.2) (split.apply_symm_apply pr.2))

end Prefix

variable {D B w : ℕ} {P : Type} {bits : P → ℕ} {N : Network D P bits}
    (sa : SignedTaskArena.Layout) {gen : Fragment IO} {n : ℕ} (S : PositiveTeam sa.id gen n w) (pr : S.Prefix) (control fieldWidth bodyCap : ℕ)
set_option quotPrecheck false
set_option autoImplicit false
local notation "pub" => S.pub
local notation "mac" => install gen n S.routines
local notation "visited" => prefixVisits S pr
local notation "reportL" => reportLayout sa.before sa.after (Fin.val (S.pub 0)) control sa.p.parameters fieldWidth bodyCap sa.cube.stop
local notation "gadgets" => sa.p.report.gadgets
local notation "nteams" => sa.cube.teams
variable {cell : N.Site → Fin sa.cube.cells}
    (slot : LiveBit N cell ↪ Slot sa.cube.n sa.cube.header.d sa.cube.header.blocks (sa.cube.h*sa.cube.b))
    (tags : N.Tables (Entry (Fin sa.p.parameters) (Fin sa.p.report.gadgets))) (x : Ports bits)
    (id : TableEntry sa.cube.n sa.cube.b sa.cube.h sa.cube.K sa.cube.s → Fin sa.p.report.gadgets)
    (words : PowerWords (Fin sa.cube.teams) (Fin sa.p.parameters) (Fin sa.p.report.gadgets) B N tags)
    (label : Fin sa.cube.cells → Label (sa.cube.n+1) sa.cube.header.d) (team : Fin sa.cube.header.d → Fin sa.cube.teams)
    (a : Path N cell sa.cube.n sa.cube.header.d sa.cube.header.blocks sa.cube.b sa.cube.h sa.cube.K sa.cube.s)
    (rc : ReceivedRows (fun _ : Fin sa.cube.teams => reportLayout sa.before sa.after (Fin.val (S.pub 0)) control sa.p.parameters fieldWidth bodyCap sa.cube.stop) sa.cube.cells)
    (hosts : ∀ j : (u : Fin sa.cube.teams) × Fin (rc.cells u).length, pathCellOwner label team a (rc.order j)=j.1)
    (t : Fin sa.cube.teams) (tapes : ∀ u : Fin sa.cube.teams, ReportTape (rc.cells u))

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


set_option synthInstance.maxSize 4000
set_option maxRecDepth 14000
set_option maxHeartbeats 2200000

/-- The observed report, sparse argument and allocation facts at one *existing*
positive prefix. The visit is reconstructed from that prefix, so its final
memory cannot be chosen independently of the later receipt. -/
structure PrefixFinishRun where
  /-- The installed layout of the receiving cell banks. -/
  banks : CellBanks.Layout
  /-- Length of the source description in the report scanner. -/
  description : ℕ
  seed : PreparedReportInput pub (visited).controls.val.2.2 (rc.cells t) cursor description
  chosenTape : tapes t=(reportReturnEquiv seed mac (visited).controls.val.2.1).symm (visited).reports
  alloc : ReportAllocation sa.before sa.after banks reportL (rc.cells t) cursor
  bankStart : banks.bankStart=sa.cube.cellBank
  bankCount : banks.cells=sa.cube.cells
  bankStride : banks.stride=sa.cube.cellStride
  frame : (pub 0).val=A.frame
  parsed : HeaderSeed sa p pub raw t.val (visited).arguments.val.2.2
  deck : CubePacket.WordPrepared X sa.id pub (visited).owned.val.2.2
  /-- The directed row assignments and field pointers passed to the open suffix. -/
  inputs : OpenSuffix.Inputs
  openPlace : OpenSuffix.Placement inputs sa.cube sa.before (pub 0).val (readings (visited).owned.val.2.2)
  openReady : OpenSuffix.Ready inputs (pub 0).val (readings (visited).owned.val.2.2) w
  wordPos : 0<w
  reportDim : sa.dim≤2^w
  reportWidth : (reportL).countWidth≤w
  marks : ∀ c∈rc.cells t, ∀ b∈c.bundles, ∀ g∈b.positions, g.parameter<2^w ∧ g.place<w
  /-- Base of the source endpoint-offset table. -/
  offsets : ℕ
  /-- First address of the array of 37 signed controls. -/
  ctl : ℕ
  /-- Address of the first live-pair entry. -/
  live : ℕ
  /-- Number of public port entries. -/
  ports : ℕ
  sortedLo : (pub 0).val+112≤ sa.p.sorted
  sortedHi : sa.p.sorted+sa.p.padded≤ sa.cube.header.packetBase
  ctlLo : (pub 0).val+112≤ ctl
  ctlHi : ctl+37≤ sa.cube.header.packetBase
  /-- Number of private geometry sorting inputs reserved by the arena. -/
  sortInputs : ℕ
  /-- Gate budget used by the geometry sorter in the arena extent. -/
  sortGates : ℕ
  /-- Gate budget of the selected finite-field reader. -/
  readerGates : ℕ
  place : sa.SparsePlacement (pub 0).val ctl
  fit : (FragmentRows.Layout.fromFrame (pub 0).val (readings (visited).reports.val.2.2)).Fits w (readings (visited).reports.val.2.2)
  pointer : readings (visited).reports.val.2.2 ((pub 0).val+92)=ctl
  controls : ∀ j : Fin 37, readings (visited).reports.val.2.2 (ctl+j.val)=sa.controls j.val
  cables : (FragmentRows.Layout.fromFrame (pub 0).val (readings (visited).reports.val.2.2)).host.count=sa.cube.cables
  rowsFit : readings (visited).reports.val.2.2 ((pub 0).val+9)≤ sa.cube.maxRows
  cells : readings (visited).reports.val.2.2 ((pub 0).val+11)=sa.cube.cells
  /-- The physical type of original sites referenced by sparse cells. -/
  Orig : Type
  /-- The placed original-site lists indexed by their physical cells. -/
  placed : ℕ → CellPacket.Placed Orig
  /-- The geometry words seen by the sparse launcher. -/
  geom : ℕ → ℕ
  /-- Supplemental records issued for each physical cell. -/
  extra : ℕ → List CellSparse.Record
  production : let parts := (ScheduleClock.argumentVisitsEquiv pub mac (visited).reports.val.2.1 (visited).reports.val.2.2).symm (visited).arguments
    ∃ src : ScheduleClock.SparseCallInput pub parts.2.1.val.2.2, ScheduleClock.ProducedRoster sa
      (sa.controlRows t.val (pub 0).val offsets ctl live ports) (readings parts.1.val.2.2) placed geom extra src
  codes : ∀ e,sa.id e=(id e).val
  vertexCap : (X).frame.count≤ sa.p.report.vertices
  digitsFit : Tally.argumentWidth sa.cube.n sa.cube.b sa.cube.h sa.cube.K sa.cube.s≤ sa.p.report.cubeWidth
  headerSize : A.header=PositiveFields.width reserve axes groups cap nteams sa.dim width
  position : A.next≤ sa.cube.header.header
  endFit : sa.endAddress w sortInputs sortGates readerGates<2^w
  teamsFit : nteams<2^w
  widthFit : width≤w

set_option maxHeartbeats 185000 in
/-- The private calls, selected packet-ID scan, and unary tally reads finish
on the *same* raw path returned by this positive preparation. Low reader
addresses are preserved except for the actual selected-operand count. The cost
is that of the selected-ID scan on this path's true directory. -/
theorem PrefixFinishRun.targetReceipt
    (run : PrefixFinishRun sa S pr control fieldWidth bodyCap id team a rc t tapes A p)
    (reads : ReportReaders slot tags x words label team a t ordering reports)
    (sourceRows : Fin sa.cube.teams → Fin sa.dim → ℕ) (numbered : rows = sourceRows)
    (bounded : ∀ c,sourceRows t c < 2^w) :
    ∃ receipt : FinishInput t sourceRows width pub mac
        (cellBank pub mac pr.2.val.2.1 pr.2.val.2.2) pr.2.val.2.2 p.tallyWords,
      receipt.post=sa.after ∧ receipt.raw=raw ∧
      receipt.operands=receiptOperands tags tablePosition words label team a t ordering reports sa.after cursor
        (pub 0).val (sa.cube.stop+1) ∧
      (∀ k < sa.after.start, k ≠ (pub 0).val+35 → receipt.selected k=pr.2.val.2.2 k) ∧
      traceCost receipt.earlier ≤ selectedOperandsTicks (X).frame.count (X).frame.width ∧
      (pub 0).val=A.frame ∧ A.next ≤ sa.cube.header.header := by
  subst sourceRows
  let packets (v : Packet sa.cube.n sa.cube.header.d sa.cube.header.blocks × Vertex (sa.cube.n+1)) :
      PacketRead :=
    let u := pathOwner label team a (.inr v)
    let i := (nativeVertexOrder label team a u).symm ⟨v,rfl⟩
    ⟨sa.after.ids+i.val,sa.cube.stop,(pub 0).val+82,sa.cube.stop+1⟩
  let result (st : Bank w × Memory w) := ∃ receipt : FinishInput t rows width pub mac
      (cellBank pub mac st.1 st.2) st.2 p.tallyWords,
    receipt.post=sa.after ∧ receipt.raw=raw ∧
    receipt.operands=receiptOperands tags tablePosition words label team a t ordering reports sa.after cursor
      (pub 0).val (sa.cube.stop+1) ∧
    (∀ k < sa.after.start, k ≠ (pub 0).val+35 → receipt.selected k=st.2 k) ∧
    traceCost receipt.earlier ≤ selectedOperandsTicks (X).frame.count (X).frame.width ∧
    (pub 0).val=A.frame ∧ A.next ≤ sa.cube.header.header
  apply (congrArg result (prefixVisits_state S pr)).mp
  obtain ⟨receipt,post,rawEq,operands,kept,clock⟩ :=
    receivedFinishFromReads sa pub control fieldWidth bodyCap slot tags x id words label team a rc hosts
      t tapes packets A p mac visited run.seed run.chosenTape run.alloc run.bankStart run.bankCount
      run.bankStride run.frame run.parsed run.deck run.inputs run.openPlace run.openReady run.wordPos
      run.reportDim run.reportWidth run.marks run.offsets run.ctl run.live run.ports run.sortedLo
      run.sortedHi run.ctlLo run.ctlHi run.place run.fit run.pointer run.controls run.cables run.rowsFit
      run.cells run.placed run.geom run.extra run.production run.codes run.vertexCap run.digitsFit
      run.headerSize run.position run.endFit run.teamsFit run.widthFit reads bounded
  exact ⟨receipt,post,rawEq,operands,kept,clock,run.frame,run.position⟩

end Cube.Physical.NativeLedger

end BorderVNP
end Computability
end OAI

import OAI.Computability.BorderVNP.DiagonalEmittedReportTransport
import OAI.Computability.BorderVNP.DiagonalNativeSavedPlacement
import OAI.Computability.BorderVNP.DiagonalSparsePlacementEvidence

/-! # Carrying the selected original call and its geometric receipt together -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.FragmentRows

open VPVNP.BurstRAM BorderVNP.Cube Evaluator Evaluator.ScheduleClock SignedTaskArena CellSparse CellSparse.Packet
open CellSparse.Packet.Source CellPacket CellPacket.Supplement DiagonalTallyAllocation SparseExterior TypedTaskBuilder
open BorderVNP.Cube.Physical BorderVNP.Cube.TeamRowClock BorderVNP.Cube.TeamRowSources
open Crossing Packing.CellAddresses Packing.Directory DiagonalTallyCellReports
open Diagonal.ExternalSew.Fragments CellPacketGeometry CellDispatch Packing.BundleDirectory
open DiagonalTallyCellReports.ReportDirectory
open TeamContraction BorderVNP.Cube.Physical BorderVNP.Cube.Scatter BorderVNP.Cube.TeamRows Scatter.Assignment FiniteEvaluator

variable {teams n w : ℕ} (a : SignedTaskArena.Layout)
    (U : Fin (teams+1) → PinStart SparseExterior.driver n w) (u : Fin (teams+1)) (p : (U u).Prefix a.id)
    (dir : Packing.Directory.Layout) (offsets ctl live ports : ℕ) (E I P A : Type)
    [Fintype P] [Fintype A] (wp wd B J : ℕ)

set_option quotPrecheck false
local notation3 (prettyPrint := false) "vis" => PinStart.visits a.id U p
local notation3 (prettyPrint := false) "orig" => (vis).reports.val.2.2
local notation3 (prettyPrint := false) "fr" => FragmentRows.Layout.fromFrame ((U u).pub 0).val (readings orig)
local notation3 (prettyPrint := false) "scan" => a.controlRows u.val ((U u).pub 0).val offsets ctl live ports
local notation3 (prettyPrint := false) "stages" =>
  (argumentVisitsEquiv (U u).pub (CompactMachine.install SparseExterior.driver n (U u).routines)
    (vis).reports.val.2.1 orig).symm (vis).arguments


open CompactMachine CellMacro.Generator

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 6500 in
/-- Package the same selected launch, issued input and two native return
banks. The geometric data and the original source reads remain attached to
the packet before the whole task is reindexed onto the physical arena. -/
noncomputable def EmittedReport.fromFundedSite
    {fit : (fr).Fits w (readings orig)} {cells : a.fragments.cells=(fr).cells}
    (emission : SparseEmission a fr orig fit cells)
    {data : ℕ → ℕ → Bool} (patch : SparsePatch (w:=w) (Fin dir.entries) scan (readings emission.output))
    (row : (i : Fin ((scan).toLayout.before (readings emission.output) a.cube.cells)) → SparseCell a fr orig data i.val)
    (declaration : LengthDeclaration a.cube.n a.cube.header.d)
    (label : Fin a.cube.cells → Label (a.cube.n+1) a.cube.header.d) (recv : A → Fin a.cube.cells) (incoming : A → ℕ)
    (layout : ReportLayout) (home : Fin J → Fin a.cube.cells) (payload : Fin J → ReportBundle)
    (external supply privateWidth : ℕ → ℕ) (digits : ℕ → Fin layout.gadgets → Fin layout.countWidth → Bool)
    (cursor : ReportCursor)
    (seed : PreparedReportInput (U u).pub (vis).controls.val.2.2
      (sourceCells layout home payload u.val ((scan).owner (readings emission.output)) external supply privateWidth digits)
      cursor dir.description)
    (launch : SparseEmission.NativeInputAt (a:=a) (team:=u.val) (frame:=((U u).pub 0).val) (offsets:=offsets)
      (ctl:=ctl) (live:=live) (ports:=ports) a.id U p emission patch row dir.description)
    {copies parameters : ℕ}
    (issued : SparseEmission.IssuedReportData (E:=E) (I:=I) (P:=P) (wp:=wp) (wd:=wd) (copies:=copies)
      (H:=parameters) (B:=B) a a.id U p emission dir patch row declaration label recv incoming layout home payload
      external supply privateWidth digits seed)
    (same : issued.native=launch.native) (banked : emission.bank=(stages).1.val.2.1)
    (emitted : emission.output=(stages).1.val.2.2) (copyCount : copies=a.cube.teams) (parameterCount : parameters=a.p.parameters)
    {tags rows₀ : ℕ} (originalDirectory : SiteWords.Directory (Fin tags) (Fin dir.entries) (rows₀+1))
    (shape : ∃ pl, TypedBatch.SourceShape pl originalDirectory ∧ patch.placed=History.Native.Terminal.placeAt pl)
    (owner : ℕ → ℕ) (owned : OwnerTable (U u).pub p.2.val.2.2 ⟨u.val,a.before.limit,a.cube.cells⟩ owner)
    {Index : Type*} (index : Index → ℕ) (want : Index → CellInput)
    (atCell : ∀ i, launch.native.logicalAt (index i)=want i) :
    {report : EmittedReport a U u p dir offsets ctl live ports E I P A wp wd B J //
      report.declaration=declaration ∧ report.label=label ∧ report.recv=recv ∧ report.incoming=incoming ∧
      report.emission=emission ∧ report.home=home ∧ report.layout=layout ∧ report.payload=payload ∧
      HEq report.seed seed ∧ report.launch.native=launch.native ∧
      OwnerTable (U u).pub p.2.val.2.2 ⟨u.val,a.before.limit,a.cube.cells⟩ owner ∧
      (∀ i,report.launch.native.logicalAt (index i)=want i) ∧
      Nonempty (SavedSparsePlacement originalDirectory report.launch.native.logicalAt)} := by
  subst copies
  subst parameters
  let report : EmittedReport a U u p dir offsets ctl live ports E I P A wp wd B J :=
    ⟨fit,cells,emission,data,patch,row,declaration,label,recv,incoming,layout,home,payload,external,supply,privateWidth,
      digits,cursor,seed,launch,issued,same,banked,emitted⟩
  refine ⟨report,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,HEq.rfl,rfl,owned,atCell,⟨⟨?_⟩⟩⟩
  exact SparseEmission.NativeInputAt.savedPlacement a.id U p emission patch row launch shape

end RoutingISA.FragmentRows

end BorderVNP
end Computability
end OAI

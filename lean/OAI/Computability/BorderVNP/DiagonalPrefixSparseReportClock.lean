import OAI.Computability.BorderVNP.DiagonalPrefixSparseLauncher
import OAI.Computability.BorderVNP.DiagonalLocalSparseReportLaunch
import OAI.Computability.BorderVNP.DiagonalVisitedReportArguments
import OAI.Computability.BorderVNP.DiagonalReachedReportCells
import OAI.Computability.BorderVNP.DiagonalVisitedReportWidths

/-! # The sparse argument and funded report source on the very same native prefix -/

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

variable {teams n w axes b h K symbols : ℕ} (id : TableEntry axes b h K symbols → ℕ)
    (U : Fin (teams+1) → PinStart SparseExterior.driver n w) {agent : Fin (teams+1)} (p : (U agent).Prefix id)
local notation3 (prettyPrint := false) "pub" => (U agent).pub
local notation3 (prettyPrint := false) "mac" => CompactMachine.install SparseExterior.driver n (U agent).routines
local notation3 (prettyPrint := false) "visit" => PinStart.visits id U p
local notation3 (prettyPrint := false) "stages" => (argumentVisitsEquiv pub mac (visit).reports.val.2.1 (visit).reports.val.2.2).symm (visit).arguments
local notation3 (prettyPrint := false) "bank" => (stages).2.1.val.2.1
local notation3 (prettyPrint := false) "buf" => (visit).controls.val.2.2

variable {a : SignedTaskArena.Layout} {f : FragmentRows.Layout} {orig : Memory w}
    {fit : f.Fits w (readings orig)} {cells : a.fragments.cells=f.cells}
    (e : SparseEmission a f orig fit cells) {frame offsets ctl live ports : ℕ} {data : ℕ → ℕ → Bool}
    (dir : Packing.Directory.Layout)

set_option quotPrecheck false
local notation "R" => a.controlRows agent.val frame offsets ctl live ports
local notation "raw" => readings e.output
local notation "num" => (R).before raw (R).cells
local notation "idx" => globalCell (R).toLayout raw
variable (patch : SparsePatch (w:=w) (Fin dir.entries) (a.controlRows agent.val frame offsets ctl live ports) (readings e.output))
    (row : (i : Fin ((a.controlRows agent.val frame offsets ctl live ports).toLayout.before (readings e.output) a.cube.cells)) →
      SparseCell a f orig data i.val)
local notation "src" => Batch.produced R raw patch.placed patch.geometry patch.extra
local notation "field" => SparseEmission.globalCells (team:=agent.val) (frame:=frame) (offsets:=offsets) (ctl:=ctl) (live:=live)
  (ports:=ports) e row
local notation "os" => fun i => field (idx i)
local notation "sl" => batchLayout a frame ctl num
local notation "task" => fun i => ((os) i).typed sl (src i).typed
local notation "logical" => fun c => SparseExterior.logicalCell (patch.placed c) (patch.extra c) (field c).field

variable {E I P A : Type} [Fintype P] {wp wd copies H B : ℕ}
    (D : LengthDeclaration a.cube.n a.cube.header.d)
    (label : Fin a.cube.cells → Label (a.cube.n+1) a.cube.header.d)
    (recv : A → Fin a.cube.cells) (incoming : A → ℕ) (assigned : ℕ → ℕ)
    {J : ℕ} (L : ReportLayout) (home : Fin J → Fin a.cube.cells) (payload : Fin J → ReportBundle)
    (eb supply privateWidth : ℕ → ℕ) (digits : ℕ → Fin L.gadgets → Fin L.countWidth → Bool)
    {q : ReportCursor} (tape : ℕ → Bool) (position : ℕ → ℕ)
local notation "owner" => scheduledCellOwner a.cube D label assigned
local notation "baseRow" => sourceCell L home payload eb supply privateWidth digits
local notation "baseReports" => sourceCells L home payload agent.val ((R).owner raw) eb supply privateWidth digits
variable (seed : PreparedReportInput (U agent).pub (PinStart.visits id U p).controls.val.2.2
    (sourceCells L home payload agent.val ((a.controlRows agent.val frame offsets ctl live ports).owner (readings e.output))
      eb supply privateWidth digits) q dir.description)
local notation "atReported" => fun c : ℕ => (baseRow c).withTape tape (position c)
local notation "sample" => fun c : Fin a.cube.cells => (atReported) c.val
local notation "sampledReports" => ((List.range a.cube.cells).filter (fun c => decide ((R).owner raw c=agent.val))).map (atReported)

variable (fp : ((U agent).pub 0).val=frame) (facts : ReachedReportCells (n:=n) e patch row dir.description)
    (address : patch.built=((argumentVisitsEquiv (U agent).pub (CompactMachine.install SparseExterior.driver n (U agent).routines)
      (PinStart.visits id U p).reports.val.2.1 (PinStart.visits id U p).reports.val.2.2).symm
      (PinStart.visits id U p).arguments).2.1.val.2.2)
    {z ns ne np nc : ℕ} {bits : P → ℕ} (N : Network z P bits) (host : N.Site → Fin a.cube.cells)
    (edge : N.Edge ↪ Fin ne) (port : P ↪ Fin np) (ord : N.CrossingEdge host ≃ Fin nc)
    (cables : CableRows N host edge port f.host (readings orig))
    (pp lp : ℕ → ℕ × ℕ)
    (physicalRows : (List.range f.count).map (f.row (readings orig))=dir.directory pp lp)
    (located : RowLocations (dir.directory pp lp) (Fin.val : Fin a.cube.cells → ℕ) recv incoming)
    (boxRows : dir.OriginalBoxRows pp (fun c : Fin a.cube.cells => patch.placed c.val))
    (bundleEntry : Fin J ↪ Fin dir.entries) (sentTo : ∀ j, (pp (bundleEntry j).val).1=(home j).val)
    (literal : 0<dir.literal/2) (descriptionFits : dir.description≤dir.literal/2)
    (pairBound : ∀ pair, load (cablePair ord (crossSrc N host) (crossDst N host) label)
      (crossWidth N host ∘ ord.symm) pair ≤ a.cube.header.blocks*(a.cube.h*a.cube.b))
    (template : LiveWords.Template E I (Fin dir.entries) ns (a.cube.cells+1))
    (site : Fin ns → Fin (a.cube.cells+1)) (arg : E → ℕ) (emit : Fin ns → I → ℕ)
    (shape : TypedBatch.SourceFootprint (fun c => patch.placed c.val) (template.directory site arg emit))
    (pubRoom : (a.cube.cells+1)+template.atoms.length+(a.cube.cells+1) ≤ 2^wp)
    (descRoom : (a.cube.cells+1)+(Schema.coords template.chunkLabels.length).length+(a.cube.cells+1) ≤ 2^wd)
    (counts : ∀ c : Fin a.cube.cells, (patch.placed c.val).reports.length=L.gadgets)
    (fieldDigits : ∀ c : Fin a.cube.cells, ∀ g ∈ (patch.placed c.val).reports, g.length=L.countWidth)
    (body : ∀ c < (a.controlRows agent.val frame offsets ctl live ports).cells,
      (a.controlRows agent.val frame offsets ctl live ports).owner (readings e.output) c=
        (a.controlRows agent.val frame offsets ctl live ports).team → ∀ j,
      (patch.placed c).headerWidth+(boxBody ((patch.placed c).factors j)).length ≤ dir.description)
    (owners : ∀ c : Fin a.cube.cells, (a.controlRows agent.val frame offsets ctl live ports).owner (readings e.output) c.val=
      scheduledCellOwner a.cube D label assigned c)
    {banks : CellBanks.Layout}
    (reportOutput : orig=(PinStart.visits id U p).reports.val.2.2)
    (tailTable : a.before.tailWidths=L.tailWidths)
    (alloc : ReportAllocation a.before a.after banks L
      (sourceCells L home payload agent.val ((a.controlRows agent.val frame offsets ctl live ports).owner (readings e.output)) eb supply privateWidth digits) q)
    (emitExtras : patch.extra=seedExtras (visitedReportRows (a.controlRows agent.val frame offsets ctl live ports)
      (readings e.output) (sourceCell L home payload eb supply privateWidth digits)) q)
    (marked : ((c : {c : Fin a.cube.cells // scheduledCellOwner a.cube D label assigned c=agent.val}) ×
      UsePositions (((sourceCell L home payload eb supply privateWidth digits c.val.val).withTape tape
        (position c.val.val)).bundles)) ↪
      Diagonal.CellEntries.PowerSlot (Fin copies) (Fin H) B)

local notation3 (prettyPrint := false) "paidReports" native =>
  ∃ S : SparseReportSources (Fin dir.entries) E I P a.cube D label recv incoming assigned agent.val dir.description
    wp wd copies H B (PinStart.SparseSource.source native) f (readings orig) R raw,
    S.LocalReadback (team:=agent) patch.geometry patch.placed patch.extra field (sample) baseReports sampledReports ∧
    PreparedReportInput pub buf (S.reportRows (team:=agent)) q dir.description

include seed fp facts address cables physicalRows located boxRows sentTo literal descriptionFits pairBound shape pubRoom
  descRoom counts fieldDigits body owners reportOutput tailTable alloc emitExtras marked

set_option maxHeartbeats 2200000 in
/-- Recover the sparse and report charges from a previously saved native
submission on the same pre-call prefix. This preserves the particular chosen
argument, including other physical readbacks retained by the caller. -/
theorem _root_.OAI.Computability.BorderVNP.RoutingISA.Evaluator.ScheduleClock.SparseReportSources.reachedFromRoster (native : PinStart.SparseSource id U p)
    (roster : ProducedRoster a R raw patch.placed patch.geometry patch.extra native.source)
    (owned : native.source.owned=os) (tasks : native.source.tasks=task) : paidReports native := by
  have finalImage : readings (stages).2.1.val.2.2=(R).toLayout.published raw := address ▸ patch.image
  have submitted : native.source.tasks=fun j =>
      (SparseExterior.supplementalRow R raw native.source.layout field patch.placed patch.geometry patch.extra j).typed := by
    rw [roster.layout]
    exact tasks
  have orderedRows : sourceCells L home payload agent.val ((R).owner raw) eb supply privateWidth digits =
      visitedReportRows R raw baseRow := (visitedReportRows_scan R raw baseRow).symm
  have rowTail (j : Fin num) : (row j).tail.length=(baseRow (row j).number.val).tailWidth := by
    have selected := global_spec (R).toLayout raw j.isLt
    have owned : (R).owner raw (row j).number.val=(R).team := (facts.ownerOrder j) ▸ selected.2.1
    have width := returned_owned_width R raw baseRow (fun _ => rfl) orderedRows alloc seed
      (visit).reports (row j).number.val (row j).number.isLt owned
    have stored := (row j).tailLength
    have memory := congrArg (fun m : Memory w => readings m (a.before.tailWidths+(row j).number.val)) reportOutput
    have address := congrArg (fun base => readings (visit).reports.val.2.2 (base+(row j).number.val)) tailTable
    exact stored.symm.trans (memory.trans (address.trans width))
  let cursor (c : Fin a.cube.cells) := visitedLocalCursor R raw (atReported) q c.val
  let base (c : Fin a.cube.cells) := L.bundleTable+6*((sample) c).first
  let source (c : Fin a.cube.cells) := visitedBundleMemory R raw (atReported) q buf c.val
  have scanned := PreparedReportInput.visitedSource R raw q baseRow seed tape position
  have bind (c : Fin a.cube.cells) (owned : owner c=agent.val) :
      patch.extra c.val=bindingRows ((sample) c).bundles (cursor c) := by
    rw [emitExtras]
    exact visited_seedExtras_sampled R raw baseRow q (fun _ => rfl) tape position c.val c.isLt ((owners c).trans owned)
  have bundles (c : Fin a.cube.cells) (owned : owner c=agent.val) :
      bundleInputs w L dir.description ((sample) c).bundles (cursor c) (base c) (source c) :=
    PreparedReportInput.ownedBundleAt R raw (atReported) scanned c.val c.isLt ((owners c).trans owned)
  exact SparseReportSources.localLaunch e agent row facts.ownerOrder pub (stages).2.1.val.2.2 dir
    patch.placed patch.geometry patch.extra D label recv incoming assigned L home payload eb supply privateWidth digits
    tape position native.source roster fp finalImage owned submitted N host edge port ord cables pp lp physicalRows located
    boxRows bundleEntry sentTo literal descriptionFits pairBound template site arg emit shape pubRoom descRoom cursor base
    source rowTail counts fieldDigits body owners bind bundles marked seed

set_option maxHeartbeats 2200000 in
/-- One physical pre-call computation supplies its original native packet, its
owner roster, the proposed report rows, their funded scanner input and the
generated calls on the returned prefix memory. -/
theorem SparseEmission.launched_report_clock_on_prefix {u v k : ℕ}
    (place : a.SparsePlacement frame ctl) (geo : SparseGeometry a f offsets ctl)
    (limit : a.endAddress w u v k<2^w)
    (word : readings orig (frame+30)=w) (controls : ∀ i : Fin 37, readings orig (ctl+i.val)=a.controls i.val)
    (taskFields : (R).toLayout.Fields raw)
    (last : Returns (.block [CellPacket.Supplement.Batch.entry,SparseExterior.prepare,TypedBatch.entry]) pub mac bank patch.built)
    (returned : last.val.2=(visit).arguments.val.2) :
    (∃ native : PinStart.SparseSource id U p,
      native.logicalAt=logical ∧
      native.bytesAt=(fun c => Packet.input ((logical) c).directory ((logical) c).privateWires (field c).field.bytes) ∧
      ProducedRoster a R raw patch.placed patch.geometry patch.extra native.source ∧
      native.source.count=num ∧ native.source.owned=os ∧ native.source.tasks=task ∧
      (∀ i : Fin num, native.source.owned i.val=(row i).owned (fit:=fit) (cells:=cells)) ∧
      paidReports native) ∧
    ∃ out : GeneratedCells SparseExterior.driver n pub p.2.val.2.2, out.cell=logical ∧
      out.payload=(fun c => Packet.input ((logical) c).directory ((logical) c).privateWires (field c).field.bytes) := by
  obtain ⟨⟨native,logicalCells,bytes,roster,len,owned,tasks,rowAt⟩,calls⟩ :=
    SparseEmission.launched_on_prefix id U p e patch row place geo limit fp word controls taskFields facts.ownerOrder facts.rank facts.publicEnd
      facts.geometry dir.description facts.originals facts.sup facts.stored facts.sizes facts.paid address last returned
  refine ⟨⟨native,logicalCells,bytes,roster,len,owned,tasks,rowAt,?_⟩,calls⟩
  exact SparseReportSources.reachedFromRoster id U p e dir patch row D label recv incoming assigned L home payload eb supply
    privateWidth digits tape position seed fp facts address N host edge port ord cables pp lp physicalRows located boxRows bundleEntry sentTo
    literal descriptionFits pairBound template site arg emit shape pubRoom descRoom counts fieldDigits body owners reportOutput
    tailTable alloc emitExtras marked native roster owned tasks

end RoutingISA.FragmentRows

end BorderVNP
end Computability
end OAI

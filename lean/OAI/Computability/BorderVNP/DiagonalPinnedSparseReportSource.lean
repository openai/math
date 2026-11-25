import OAI.Computability.BorderVNP.DiagonalPrefixSparseReportClock
import OAI.Computability.BorderVNP.DiagonalScheduledEmissionOwners
import OAI.Computability.BorderVNP.DiagonalReturnedSparseReportClock

/-! # A saved physical argument source on the particular attained public owner schedule -/

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
    (id : TableEntry a.cube.n a.cube.b a.cube.h a.cube.K a.cube.s → ℕ)
    (U : Fin (teams+1) → PinStart SparseExterior.driver n w) {agent : Fin (teams+1)} (p : (U agent).Prefix id)

local notation3 (prettyPrint := false) "pub" => (U agent).pub
local notation3 (prettyPrint := false) "frame" => ((U agent).pub 0).val
local notation3 (prettyPrint := false) "mac" => CompactMachine.install SparseExterior.driver n (U agent).routines
local notation3 (prettyPrint := false) "v" => PinStart.visits id U p
local notation3 (prettyPrint := false) "orig" => (v).reports.val.2.2
local notation3 (prettyPrint := false) "buf" => (v).controls.val.2.2
local notation3 (prettyPrint := false) "stages" => (argumentVisitsEquiv pub mac (v).reports.val.2.1 orig).symm (v).arguments
local notation3 (prettyPrint := false) "f" => FragmentRows.Layout.fromFrame frame (readings orig)

variable {fit : (FragmentRows.Layout.fromFrame ((U agent).pub 0).val (readings (PinStart.visits id U p).reports.val.2.2)).Fits w
      (readings (PinStart.visits id U p).reports.val.2.2)}
    {cells : a.fragments.cells=(FragmentRows.Layout.fromFrame ((U agent).pub 0).val (readings (PinStart.visits id U p).reports.val.2.2)).cells}
    (e : SparseEmission a (FragmentRows.Layout.fromFrame ((U agent).pub 0).val (readings (PinStart.visits id U p).reports.val.2.2))
      (PinStart.visits id U p).reports.val.2.2 fit cells)
    {offsets ctl live ports : ℕ} {data : ℕ → ℕ → Bool} (dir : Packing.Directory.Layout)
set_option quotPrecheck false
local notation "R" => a.controlRows agent.val frame offsets ctl live ports
local notation "raw" => readings e.output
local notation "num" => (R).before raw (R).cells
local notation "idx" => globalCell (R).toLayout raw
variable (patch : SparsePatch (w:=w) (Fin dir.entries) (a.controlRows agent.val ((U agent).pub 0).val offsets ctl live ports) (readings e.output))
    (row : (i : Fin ((a.controlRows agent.val ((U agent).pub 0).val offsets ctl live ports).toLayout.before (readings e.output) a.cube.cells)) →
      SparseCell a (FragmentRows.Layout.fromFrame ((U agent).pub 0).val (readings (PinStart.visits id U p).reports.val.2.2))
        (PinStart.visits id U p).reports.val.2.2 data i.val)
local notation "src" => Batch.produced R raw patch.placed patch.geometry patch.extra
local notation "field" => SparseEmission.globalCells (team:=agent.val) («frame»:=frame) (offsets:=offsets) (ctl:=ctl) (live:=live)
  (ports:=ports) e row
local notation "os" => fun i => field (idx i)
local notation "sl" => batchLayout a frame ctl num
local notation "task" => fun i => ((os) i).typed sl (src i).typed
local notation "logical" => fun c => SparseExterior.logicalCell (patch.placed c) (patch.extra c) (field c).field

variable {E I P A : Type} [Fintype P] [Fintype A] {wp wd copies H B : ℕ}
    (D : LengthDeclaration a.cube.n a.cube.header.d)
    (label : Fin a.cube.cells → Label (a.cube.n+1) a.cube.header.d)
    (recv : A → Fin a.cube.cells) (incoming : A → ℕ) (assigned : ℕ → ℕ)
    {J : ℕ} (L : ReportLayout) (home : Fin J → Fin a.cube.cells) (payload : Fin J → ReportBundle)
    (eb supply privateWidth : ℕ → ℕ) (digits : ℕ → Fin L.gadgets → Fin L.countWidth → Bool)
    {q : ReportCursor}
local notation "baseRow" => sourceCell L home payload eb supply privateWidth digits
local notation "baseReports" => sourceCells L home payload agent.val ((R).owner raw) eb supply privateWidth digits
variable (seed : PreparedReportInput ((U agent).pub) (PinStart.visits id U p).controls.val.2.2
    (sourceCells L home payload agent.val ((a.controlRows agent.val ((U agent).pub 0).val offsets ctl live ports).owner
      (readings e.output)) eb supply privateWidth digits) q dir.description)
local notation "tape" => seed.returnedTape (v).reports
local notation "position" => returnedTapePosition R raw baseReports
local notation "atReported" => fun c : ℕ => (baseRow c).withTape tape (position c)
local notation "sample" => fun c : Fin a.cube.cells => (atReported) c.val
local notation "actualReports" => ((assignedReportReturnEquiv seed mac (v).controls.val.2.1).symm (v).reports).val
local notation "physOwner" => greedyOwner teams a.cube.b a.cube.s label recv incoming

set_option maxHeartbeats 1400000 in
set_option maxRecDepth 5200 in
/-- Bind the native sparse input to the owner array selected by this actual
public weight run. The pre-scan records and original marks use only the genuine
physical grouping. The report and argument share a source with the caller's
previously recovered private-cell roster. -/
theorem SparseEmission.sourcesOnScheduledPrefix
    (native : PinStart.SparseSource id U p)
    (roster : ProducedRoster a R raw patch.placed patch.geometry patch.extra native.source)
    (owned : native.source.owned=os) (tasks : native.source.tasks=task)
    (facts : ReachedReportCells (n:=n) e patch row dir.description) (address : patch.built=(stages).2.1.val.2.2)
    {profile : ℕ → ℕ} {group : Fin a.cube.header.d → Fin (teams+1)}
    {family : TeamRows.Returns (Fin (teams+1)) a.cube w} {rowBits : Symbols a.cube.header.d → List Bool}
    {assignment : NativeAssignments.Routed (b:=a.cube.b) (s:=a.cube.s) physOwner}
    (observed : ObservedOwned a.cube D group family physOwner rowBits assignment)
    (schedule : GroupWeights.ScheduleResult (LocalRow.weightLayout a.cube frame D.1.val) (LocalRow.teamLayout a.cube teams) profile assigned)
    (image : GroupWeights.PhysicalImage (LocalRow.weightLayout a.cube frame D.1.val) profile
      a.cube.header.blocks a.cube.b a.cube.K a.cube.h D label recv incoming)
    {headerBits : ℕ} (header : Fin J → Packing.BottomReports.BundleHeader)
    (room : a.OpenRoom frame offsets ctl live ports J (2^headerBits) w)
    (place : OpenSuffix.Placement (a.openInputs agent.val frame offsets ctl live ports J headerBits home header)
      a.cube a.before frame (readings (v).owned.val.2.2))
    (ready : OpenSuffix.Ready (a.openInputs agent.val frame offsets ctl live ports J headerBits home header)
      frame (readings (v).owned.val.2.2) w)
    (ptr : readings orig (frame+92)=ctl)
    (ownerWord : ∀ c : Fin a.cube.cells, readings (v).owned.val.2.2 (a.cube.hostDirectory+2*c.val)=
      ((physOwner) assignment.1 (label c (chosen a.cube.b a.cube.s assignment.1))).val)
    {z ns ne np nc : ℕ} {bits : P → ℕ} (N : Network z P bits) (host : N.Site → Fin a.cube.cells)
    (edge : N.Edge ↪ Fin ne) (port : P ↪ Fin np) (ord : N.CrossingEdge host ≃ Fin nc)
    (cables : CableRows N host edge port (f).host (readings orig))
    (pp lp : ℕ → ℕ × ℕ)
    (physicalRows : (List.range (f).count).map ((f).row (readings orig))=dir.directory pp lp)
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
    (body : ∀ c < (R).cells, (R).owner raw c=(R).team → ∀ j,
      (patch.placed c).headerWidth+(boxBody ((patch.placed c).factors j)).length ≤ dir.description)
    (tailTable : a.before.tailWidths=L.tailWidths)
    (alloc : ReportAllocation a.before a.after (a.cube.cellWriter frame ctl D.1) L baseReports q)
    (emitExtras : patch.extra=seedExtras (visitedReportRows R raw baseRow) q)
    (sourceMarks : ((c : {c : Fin a.cube.cells // (group (label c D.1)).val=agent.val}) × UsePositions (((sample) c.val).bundles)) ↪
      Diagonal.CellEntries.PowerSlot (Fin copies) (Fin H) B) :
    ∃ S : SparseReportSources (Fin dir.entries) E I P a.cube D label recv incoming assigned agent.val dir.description
      wp wd copies H B native.source f (readings orig) R raw,
      ProducedRoster a R raw S.places S.geometry S.extra native.source ∧
      PreparedReportInput pub buf (S.reportRows (team:=agent)) q dir.description ∧
      S.LocalReadback (team:=agent) patch.geometry patch.placed patch.extra field (sample) baseReports actualReports := by
  have axis : chosen a.cube.b a.cube.s assignment.1=D.1 := congrArg Prod.fst observed.observed.1
  have source (c : Fin a.cube.cells) : readings (v).owned.val.2.2 (a.cube.hostDirectory+2*c.val)=(group (label c D.1)).val := by
    rw [ownerWord c,axis,observed.allocation]
  have real := (v).scheduledOwners_at_emission a home header label recv incoming observed schedule image
    room place ready seed alloc e ptr source
  have legal : passesLengths a.cube.b a.cube.s assignment.1 D := (passesLengths_iff ..).mpr observed.observed.1.symm
  have scheduleOwner : scheduledCellOwner a.cube D label assigned=(fun c => (group (label c D.1)).val) := by
    funext c
    exact (greedyOwner_stored schedule assignment.1 legal label recv incoming image (label c D.1)).trans
      (congrArg (fun h => (h (label c D.1)).val) observed.allocation)
  have marks : ((c : {c : Fin a.cube.cells // scheduledCellOwner a.cube D label assigned c=agent.val}) × UsePositions (((sample) c.val).bundles)) ↪
      Diagonal.CellEntries.PowerSlot (Fin copies) (Fin H) B := scheduleOwner ▸ sourceMarks
  obtain ⟨S,scanned,prepared⟩ := SparseReportSources.reachedFromRoster id U p e dir patch row D label recv incoming assigned
    L home payload eb supply privateWidth digits tape position seed rfl facts address N host edge port ord cables pp lp physicalRows
    located boxRows bundleEntry sentTo literal descriptionFits pairBound template site arg emit shape pubRoom descRoom counts fieldDigits
    body real rfl tailTable alloc emitExtras marks native roster owned tasks
  exact ⟨S,SparseReportSources.LocalReadback.returnedRoster S patch.placed patch.geometry patch.extra field baseRow seed (v).reports
    (visitedReportRows_scan R raw baseRow).symm roster prepared scanned⟩

end RoutingISA.FragmentRows

end BorderVNP
end Computability
end OAI

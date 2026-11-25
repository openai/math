import OAI.Computability.BorderVNP.DiagonalIssuedArgumentWindow
import OAI.Computability.BorderVNP.DiagonalIssuedSourcePost
import OAI.Computability.BorderVNP.DiagonalPublishedPostInputs
import OAI.Computability.BorderVNP.DiagonalDeployedFeasiblePost

/-! # Passing the native issued report and published election to the actual post-call bound -/

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
    (U : Fin (teams+1) → PinStart SparseExterior.driver n w) {agent : Fin (teams+1)} (p : (U agent).Prefix a.id)

local notation3 (prettyPrint := false) "pub" => (U agent).pub
local notation3 (prettyPrint := false) "frame" => ((U agent).pub 0).val
local notation3 (prettyPrint := false) "mac" => CompactMachine.install SparseExterior.driver n (U agent).routines
local notation3 (prettyPrint := false) "v" => PinStart.visits a.id U p
local notation3 (prettyPrint := false) "orig" => (v).reports.val.2.2
local notation3 (prettyPrint := false) "buf" => (v).controls.val.2.2
local notation3 (prettyPrint := false) "stages" => (argumentVisitsEquiv pub mac (v).reports.val.2.1 orig).symm (v).arguments
local notation3 (prettyPrint := false) "f" => FragmentRows.Layout.fromFrame frame (readings orig)

variable {fit : (FragmentRows.Layout.fromFrame ((U agent).pub 0).val (readings (PinStart.visits a.id U p).reports.val.2.2)).Fits w
      (readings (PinStart.visits a.id U p).reports.val.2.2)}
    {cells : a.fragments.cells=(FragmentRows.Layout.fromFrame ((U agent).pub 0).val (readings (PinStart.visits a.id U p).reports.val.2.2)).cells}
    (e : SparseEmission a (FragmentRows.Layout.fromFrame ((U agent).pub 0).val (readings (PinStart.visits a.id U p).reports.val.2.2))
      (PinStart.visits a.id U p).reports.val.2.2 fit cells)
    {offsets ctl live ports : ℕ} {data : ℕ → ℕ → Bool} (dir : Packing.Directory.Layout)
set_option quotPrecheck false
local notation "R" => a.controlRows agent.val frame offsets ctl live ports
local notation "raw" => readings e.output
local notation "num" => (R).before raw (R).cells
local notation "idx" => globalCell (R).toLayout raw
variable (patch : SparsePatch (w:=w) (Fin dir.entries) (a.controlRows agent.val ((U agent).pub 0).val offsets ctl live ports) (readings e.output))
    (row : (i : Fin ((a.controlRows agent.val ((U agent).pub 0).val offsets ctl live ports).toLayout.before (readings e.output) a.cube.cells)) →
      SparseCell a (FragmentRows.Layout.fromFrame ((U agent).pub 0).val (readings (PinStart.visits a.id U p).reports.val.2.2))
        (PinStart.visits a.id U p).reports.val.2.2 data i.val)
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
variable (seed : PreparedReportInput ((U agent).pub) (PinStart.visits a.id U p).controls.val.2.2
    (sourceCells L home payload agent.val ((a.controlRows agent.val ((U agent).pub 0).val offsets ctl live ports).owner
      (readings e.output)) eb supply privateWidth digits) q dir.description)
local notation "tape" => seed.returnedTape (v).reports
local notation "position" => returnedTapePosition R raw baseReports
local notation "atReported" => fun c : ℕ => (baseRow c).withTape tape (position c)
local notation "sample" => fun c : Fin a.cube.cells => (atReported) c.val
local notation "actualReports" => ((assignedReportReturnEquiv seed mac (v).controls.val.2.1).symm (v).reports).val
local notation "physOwner" => greedyOwner teams a.cube.b a.cube.s label recv incoming

open RoutingISA.Transmission TeamContraction.ProcessorSlots TeamContraction.JointHeader
open Diagonal.Layout Routing DiagonalTallyPacketEmit TeamScales BorderVNP.Cube.Tally
set_option maxHeartbeats 3300000
set_option maxRecDepth 7500

variable {r t d link inner : ℕ} {Edge : Type} {G : Wiring teams r t d link inner n Edge} {col : Fin d → Bool}
  {wire : WireLayout (teams+1) r link} {common : List Bool}
  {publicAt : HeaderExterior wire common → Fin (teams+1) → Arg → Word w}
  {macroAt : HeaderExterior wire common → Fin (teams+1) → TeamOpcode.Macros w 8}
  {regsAt : HeaderExterior wire common → Fin (teams+1) → Bank w}
  {memAt : HeaderExterior wire common → Fin (teams+1) → Memory w}
  (F : PreparationFrame G wire a.cube D common col publicAt macroAt regsAt memAt)
  (origin : HeaderExterior wire common) (ext : Exterior teams r link → Bool)
  {proto : DiagonalTallyPacketEmit.Frame} {amount : ℕ}
  (route : NativeAssignments.Routed (b:=a.cube.b) (s:=a.cube.s) (greedyOwner teams a.cube.b a.cube.s label recv incoming))
  (active : PinStart.JointPrefix a.id U)
  (owned : F.ReturnedOwnershipAt a origin ext proto amount route (PinStart.ownedVisits (ar:=a.cube) U active))

include owned in
/-- The submitted argument and the native post-call executions share the same
original grouped source, in the order in which the local scanner actually
issued it. No check of a proposed report or subtotal is needed before its
post-call clock is charged. -/
theorem obtained_issued_post (thisPrefix : p=active agent)
    {X budget : ℕ} (issued : SparseEmission.IssuedReportData (E:=E) (I:=I) (P:=P) (wp:=wp) (wd:=wd)
      (copies:=a.cube.teams) (H:=a.p.parameters) (B:=B) a a.id U p e dir patch row D label recv incoming
      L home payload eb supply privateWidth digits seed)
    (published : PinStart.PublishedArgumentWindow a a.id U p D label recv incoming X dir.description wp wd
      a.cube.teams a.p.parameters B f R raw budget)
    (banked : e.output=(stages).1.val.2.2)
    (physicalLayout : L=reportLayout a.before a.after frame ctl a.p.parameters a.p.siteWidth a.p.bodyCap a.cube.stop)
    (directory : F.dataDir=dir)
    (marked : ∀ x∈baseReports, ∀ y∈x.bundles, ∀ z∈y.positions, z.parameter<2^w ∧ z.place<w)
    (reported : IssuedReportFrame a pub (v).reports.val.2.2 offsets ctl (F.dataDir.directory F.privatePlacement F.livePlacement).length)
    {reserve axes groups cap query guesses gates indexWidth parameters scalars : ℕ} (startup : StartupArena)
    (fields : PositiveFields reserve axes groups cap a.cube.teams a.dim w)
    (headEq : frame=startup.frame) (demand : ℕ)
    {boot : Memory w}
    (sourceWords : (ReaderKept startup (6+3*gates+query) indexWidth boot ((U agent).pins p.1).val.2.2 (v).owned.val.2.2 ∧
       SignedTaskArena.HeaderSeed a fields pub (SignedTaskArena.rawAddress startup reserve axes groups cap) agent.val
         (v).owned.val.2.2) ∧ ∀ count, LookupPointers (a.lookupFrame count) a.after.ids frame (F.source origin agent))
    {batch length logPower readerTicks : ℕ} {α ξ : ℝ}
    (sf : a.DeployedFeasiblePost startup dir ctl reserve axes groups cap w query guesses gates indexWidth batch wp wd B X
      ⌈publicWork (a.cube.n+1) α batch length (teams+1)⌉₊
      ⌈localWork (a.cube.n+1) logPower α ξ batch length (teams+1)⌉₊ readerTicks (teams+1) parameters scalars) :
    let P₀ := ⌈publicWork (a.cube.n+1) α batch length (teams+1)⌉₊
    let L₀ := ⌈localWork (a.cube.n+1) logPower α ξ batch length (teams+1)⌉₊
    let F₀ := cubeCoefficient a.cube.n a.cube.b a.cube.h a.cube.K a.cube.s
      (argumentWidth a.cube.n a.cube.b a.cube.h a.cube.K a.cube.s)
    let H₀ := TeamRowClock.physicalCoefficient a.cube.n a.cube.b a.cube.h a.cube.K a.cube.s
    traceCost (PinStart.afterRoute a.id U p).val.1+privateDirectoryTicks pub (PinStart.afterRoute a.id U p).val.2.2≤budget ∧
      ReaderKept startup (6+3*gates+query) indexWidth boot ((U agent).pins p.1).val.2.2 p.2.val.2.2 ∧
      ∀ (call : Returns callOwnedCells pub mac p.2.val.2.1 p.2.val.2.2)
        (run : Returns (finishExpansion signedOccurrences) pub mac call.val.2.1 call.val.2.2),
        Nonempty (PinStart.PhysicalPost (d:=parameters+scalars) (width:=w) agent a P₀ L₀ F₀ H₀ pub mac call.val.2.1 call.val.2.2 run) := by
  subst p
  let reached := PinStart.issued_argument_on_pinned_prefix a a.id U (active agent) e dir patch row D
    label recv incoming L home payload eb supply privateWidth digits seed issued published
  have numbers : L.zeroAddr=a.cube.stop ∧ L.countWidth=w ∧ L.parameters=a.p.parameters ∧ L.gadgets=a.p.report.gadgets := by
    rw [physicalLayout]
    exact sf.report frame
  have directoryRoom : (F.dataDir.directory F.privatePlacement F.livePlacement).length ≤ a.cube.maxRows := by
    rw [directory]
    exact (Nat.le_add_right _ _).trans (sf.directories _ _)
  obtain ⟨argCost,protectedWords,finish⟩ := PinStart.post_on_issued_sources a U active sf.teamCount agent offsets ctl live ports F origin ext route owned
    home issued.header D.1 rfl X sf.positive sf.alphabet budget banked reached issued.allocation demand sourceWords.2
    issued.place issued.ready numbers.1 numbers.2.1.le marked reported directoryRoom startup sf.addresses fields headEq numbers.2.2
    sourceWords.1 sf.readerCopied sf.readerIndices sf.windows
  exact ⟨argCost,protectedWords,fun call run => (finish call run).map (fun paid => paid.reindex rfl sf.dimension rfl)⟩

end RoutingISA.FragmentRows

end BorderVNP
end Computability
end OAI

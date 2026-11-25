import OAI.Computability.BorderVNP.DiagonalSelectedSitePrefixRun
import OAI.Computability.BorderVNP.DiagonalFrameSourceOwnedAt
import OAI.Computability.BorderVNP.DiagonalReceivedFrameAllocation
import OAI.Computability.BorderVNP.DiagonalReportCutLayoutCast

/-! # Issuing the original prefix from the selected frame's reached report operands -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout Routing RoutingISA RoutingISA.Evaluator RoutingISA.Transmission RoutingISA.Evaluator.SignedPrep
open BorderVNP.Cube Physical Physical.NativeAssignments Scatter Scatter.Assignment JointHeader PackedHistoryCircuit LocalRow Crossing
open DiagonalTallyPacketEmit FiniteEvaluator
open scoped BigOperators

variable {R r t d link inner n w volume : ℕ} {Edge : Type} (G : Wiring R r t d link inner n Edge)
    (skeleton : WireLayout (R+1) r link) (header : List Bool) (task : SignedTaskArena.Layout)
    (D : Packing.Directory.Layout) (pp lp : ℕ → ℕ × ℕ)
    (pin : Fin d → Bool) (guess : Fin (R+1) → ℕ → Bool) (dst ib hb sb : Fin (R+1) → ℕ)
    (frame receivingBase : ℕ) (owner : ℕ → Fin (R+1)) (word : Broadcast task.cube.n task.cube.header.d task.cube.header.cap)
    (pub : HeaderExterior skeleton header → Fin (R+1) → Arg → Word w)
    (mac : HeaderExterior skeleton header → Fin (R+1) → TeamOpcode.Macros w 8)
    (reg : HeaderExterior skeleton header → Fin (R+1) → Bank w) (mem : HeaderExterior skeleton header → Fin (R+1) → Memory w)
    {I : Type*} [Fintype I] (host : I → Fin task.cube.cells) (key : I ↪ ℕ) (sizes : I → ℕ)
    {dim : ℕ} {P A : Type} {bits : P → ℕ} [Fintype A] [Fintype P] (N : Network dim P bits) (cell : N.Site → Fin task.cube.cells)
    (recv : A → Fin task.cube.cells) (amount : A → ℕ)

variable (positive : 0<task.cube.header.d)
open MotifBase MeanChoice GroupWeights
open Packing.CellAddresses Packing.CellAddressCircuit Packing.CellAddressPhysical Packing.RoutingOutputs
open Diagonal.ExternalSew.Fragments
open Packing.BottomReports DiagonalTallyCellReports DiagonalTallyAllocation ReportDirectory
open RoutingISA.CompactMachine CellMacro.Generator ProcessorSlots JointHeader Physical.NativeLedger
open FiniteEvaluator Physical.NativeAssignments SignedTaskArena Packing.Inherited Packing.Inherited.Placement
local notation3 (prettyPrint := false) "label" => meanPackedLabel N cell recv amount (List.finRange task.cube.cells)
  task.cube.n task.cube.header.d positive

set_option quotPrecheck false
local notation "ar" => task.cube
local notation3 (prettyPrint := false) "decl" => Prod.mk (Fin.ofNat (task.cube.n+1) (readCode (task.cube.n+1) word.1))
  (fun (p : Sym2 (Fin task.cube.header.d)) (j : Fin (task.cube.n+1)) => readCode (task.cube.header.cap+1) (word.2 p j))
local notation3 (prettyPrint := false) "grp" => declaredTeam ar decl label recv amount R
local notation3 (prettyPrint := false) "own" => greedyOwner R task.cube.b task.cube.s label recv amount
local notation "count" => (D.directory pp lp).length
local notation "total" => count+task.cube.header.d.choose 2
local notation "X" => HeaderExterior skeleton header
local notation3 (prettyPrint := false) "PL" u => G.pinLayout u (ib u) (hb u) (sb u)
local notation3 (prettyPrint := false) "BF" u => G.transferFrame u skeleton.header (dst u)

variable (wire : WireLayout (R+1) r link) (same : wire.header=skeleton.header)
local notation3 (prettyPrint := false) "back" => (HeaderExterior.changeLayout skeleton wire same header).symm


set_option maxHeartbeats 1800000
set_option maxRecDepth 7000

local notation3 (prettyPrint := false) "atSite(" x "," u ")" => CandidateSite («X»:=volume) ar D pp lp word owner decl grp frame receivingBase
    (PL u) (G.processorFields u pin (Subtype.val x) (ib u) (hb u) (sb u)) (BF u) (guess u) (pub x u) (mac x u)
    (reg x u) (mem x u) host key sizes N cell recv amount

open RoutingISA.SignedTaskArena Physical.NativeLedger RoutingISA.Evaluator.SignedPrep
open DiagonalTallyCellReports

variable (arena : StartupArena)
    (headerData : PositiveFields task.cube.header.profile task.cube.n task.cube.header.d task.cube.header.cap
      task.cube.teams task.dim w) (claim : Fin (task.cube.teams*task.dim*w) → Bool)
    (previous : Fin 81 → VPVNP.BurstRAM.Word w) (origin fresh geomGates outputs field off ell literalCtl : ℕ)
    (fixed : Routing.Block (R+1))
    (F : PreparationFrame G wire task.cube (Prod.mk (Fin.ofNat (task.cube.n+1) (readCode (task.cube.n+1) word.1)) (fun (p : Sym2 (Fin task.cube.header.d)) (j : Fin (task.cube.n+1)) => readCode (task.cube.header.cap+1) (word.2 p j))) header pin (pub ∘ (HeaderExterior.changeLayout skeleton wire same header).symm) (mac ∘ (HeaderExterior.changeLayout skeleton wire same header).symm) (reg ∘ (HeaderExterior.changeLayout skeleton wire same header).symm) (mem ∘ (HeaderExterior.changeLayout skeleton wire same header).symm))
    (origins : Fin (R+1) → ℕ)
    {cb lb widthO outCount ns np : ℕ} {σ : Type} [Fintype σ] (progState : N.Site → Packing.Inherited.Site)
    (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin task.cube.cables) (portID : P ↪ Fin np)
    (geom : Fields ns task.cube.cables np task.cube.cells cb lb widthO σ)
    (geometryInput : HeaderExterior wire header → Fin (R+1) → σ → Bool)
    (original : Fin D.entries → N.Site) (live : Fin (D.teams*D.sites) → P)
    (reportHost : Fin D.entries → Fin task.cube.cells) (hdr : Fin D.entries → BundleHeader)
    (body factors : Fin D.entries → List CellSparse.Factor) {b gap : ℕ}
    (slot : LiveBit N cell ↪ Slot task.cube.n task.cube.header.d task.cube.header.blocks (task.cube.h*task.cube.b))

local notation3 (prettyPrint := false) "frozen" => fun j : Fin D.entries => physicalBundle (hdr j) (body j) (factors j) (fun _ => false)
local notation3 (prettyPrint := false) "ctl(" u ")" => controlsBase (origins u) task.cube.cables task.cube.cells D.entries (D.teams*D.sites)
local notation3 (prettyPrint := false) "report(" x "," u ")" => reportLayout task.before task.after x (ctl(u)) task.p.parameters task.p.siteWidth task.p.bodyCap task.cube.stop
local notation3 (prettyPrint := false) "source" => routedSourceReports task.cube N cell own slot label
  (fun u => report(frame,u)) reportHost frozen (fun c => suppliedSize N (fun v => (cell v).val) c)
  (fun c => guessedSize N (fun v => (cell v).val) c+siteSize N (fun v => (cell v).val) c (fun v => ((progState v).size)))

variable (builders : F.Builders fixed task.id (greedyOwner R task.cube.b task.cube.s (meanPackedLabel N cell recv amount (List.finRange task.cube.cells) task.cube.n task.cube.header.d positive) recv amount)) (agree : F.SourceAgreement fixed (routedSourceReports task.cube N cell (greedyOwner R task.cube.b task.cube.s (meanPackedLabel N cell recv amount (List.finRange task.cube.cells) task.cube.n task.cube.header.d positive) recv amount) slot (meanPackedLabel N cell recv amount (List.finRange task.cube.cells) task.cube.n task.cube.header.d positive)
    (fun u : Fin (R+1) => reportLayout task.before task.after frame (controlsBase (origins u) task.cube.cables task.cube.cells D.entries (D.teams*D.sites)) task.p.parameters task.p.siteWidth task.p.bodyCap task.cube.stop) reportHost (fun j : Fin D.entries => physicalBundle (hdr j) (body j) (factors j) (fun _ => false))
    (fun c => suppliedSize N (fun v => (cell v).val) c) (fun c => guessedSize N (fun v => (cell v).val) c+siteSize N (fun v => (cell v).val) c (fun v => ((progState v).size)))) builders)
  (q : {v : Declared task.cube (greedyOwner R task.cube.b task.cube.s (meanPackedLabel N cell recv amount (List.finRange task.cube.cells) task.cube.n task.cube.header.d positive) recv amount) (Prod.mk (Fin.ofNat (task.cube.n+1) (readCode (task.cube.n+1) word.1)) (fun (p : Sym2 (Fin task.cube.header.d)) (j : Fin (task.cube.n+1)) => readCode (task.cube.header.cap+1) (word.2 p j))) // (routedSourceReports task.cube N cell (greedyOwner R task.cube.b task.cube.s (meanPackedLabel N cell recv amount (List.finRange task.cube.cells) task.cube.n task.cube.header.d positive) recv amount) slot (meanPackedLabel N cell recv amount (List.finRange task.cube.cells) task.cube.n task.cube.header.d positive)
    (fun u : Fin (R+1) => reportLayout task.before task.after frame (controlsBase (origins u) task.cube.cables task.cube.cells D.entries (D.teams*D.sites)) task.p.parameters task.p.siteWidth task.p.bodyCap task.cube.stop) reportHost (fun j : Fin D.entries => physicalBundle (hdr j) (body j) (factors j) (fun _ => false))
    (fun c => suppliedSize N (fun v => (cell v).val) c) (fun c => guessedSize N (fun v => (cell v).val) c+siteSize N (fun v => (cell v).val) c (fun v => ((progState v).size)))).pins v.val}) (reports : (routedSourceReports task.cube N cell (greedyOwner R task.cube.b task.cube.s (meanPackedLabel N cell recv amount (List.finRange task.cube.cells) task.cube.n task.cube.header.d positive) recv amount) slot (meanPackedLabel N cell recv amount (List.finRange task.cube.cells) task.cube.n task.cube.header.d positive)
    (fun u : Fin (R+1) => reportLayout task.before task.after frame (controlsBase (origins u) task.cube.cables task.cube.cells D.entries (D.teams*D.sites)) task.p.parameters task.p.siteWidth task.p.bodyCap task.cube.stop) reportHost (fun j : Fin D.entries => physicalBundle (hdr j) (body j) (factors j) (fun _ => false))
    (fun c => suppliedSize N (fun v => (cell v).val) c) (fun c => guessedSize N (fun v => (cell v).val) c+siteSize N (fun v => (cell v).val) c (fun v => ((progState v).size)))).actual q.val.val)

local notation3 (prettyPrint := false) "packet" => headerData.withSubtotals claim
local notation3 (prettyPrint := false) "rawBase" => rawAddress arena task.cube.header.profile task.cube.n
  task.cube.header.d task.cube.header.cap
local notation3 (prettyPrint := false) "old(" u ")" => routingExtension (task.extension rawBase (Fin.val u) w previous)
  D origin task.cube.cables task.cube.cells
local notation3 (prettyPrint := false) "payload" => declaredWords ar own decl q.val
local notation3 (prettyPrint := false) "replayed" => F.replay fixed payload
local notation3 (prettyPrint := false) "full" => (F.sourceEquiv fixed source builders agree).symm ⟨q,reports⟩
local notation3 (prettyPrint := false) "vis" => fun u => (visitsEquiv task.id ((pub ∘ back) full.1 u)
  ((mac ∘ back) full.1 u) ((reg ∘ back) full.1 u) ((mem ∘ back) full.1 u)).symm (full.2 u)
variable (T : PositiveTeam task.id SparseExterior.driver n w) (pr : T.Prefix)
local notation3 (prettyPrint := false) "orig" => prefixVisits T pr
local notation3 (prettyPrint := false) "fr" => (T.pub 0).val
local notation3 (prettyPrint := false) "tables(" u ")" => bases (origins u) task.cube.cables task.cube.cells D.entries
local notation3 (prettyPrint := false) "frameCast(" u "," h ")" => congrArg (fun v => report(v,u)) h
local notation3 (prettyPrint := false) "ownedBy(" eqn ")" => (finCongr eqn) ∘ own q.val.val.1
local notation3 (prettyPrint := false) "observedPath(" programs "," hidden ")" => rawPath N cell edgeID programs own q.val.val hidden

set_option maxRecDepth 9000
set_option maxHeartbeats 4000000


/-- Read the uncast source allocation, marked bits and report tape on the same
physical layout that issued them. The selected site's public register gives the
current processor frame when the decoded ownership return is identified. -/
theorem PreparationFrame.SelectedLookupSites.issueSourcePrefix
    {Trace : HeaderExterior skeleton header → Fin (R+1) → Type}
    (snap : ∀ x u, Trace x u → RoutingISA.Bank w × VPVNP.BurstRAM.Memory w)
    (charge : ∀ x u, Trace x u → ℕ × ℕ)
    (tail : ∀ (x : HeaderExterior skeleton header) (u : Fin (R+1)), atSite(x,u) → Trace x u → Prop)
    (chosen : F.SelectedLookupSites G skeleton header task D pp lp pin guess dst ib hb sb frame receivingBase
      owner word pub mac reg mem host key sizes N cell label recv amount wire same (fun x u site =>
        ∃ trace : Trace x u,
          site.OnReturn old(u) fresh geomGates outputs field off ell literalCtl (List.ofFn (packet).profile)
              (DiagonalTallyRAM.broadcast w (packet).rawCounts) 0 (snap x u trace).1 (snap x u trace).2
              (charge x u trace).1 (charge x u trace).2 ∧ tail x u site trace))
    (reached : F.CandidateReportsOnReplay (G:=G) (L:=wire) (header:=header) (pin:=pin) (d:=D) (pp:=pp) (lp:=lp)
      (pub:=pub ∘ back) (mac:=mac ∘ back) (reg:=reg ∘ back) (mem:=mem ∘ back)
      (initialBase:=frame) (receiving:=receivingBase) (pins:=fun j => PL j)
      (fields:=fun y j => G.processorFields j pin (back y).val (ib j) (hb j) (sb j))
      (bf:=fun j => BF j) (guess:=guess) (resides:=host) (key:=key) (sizes:=sizes)
      (representative:=owner) (group:=grp) (b:=b) (gap:=gap) (outputs:=outCount) fixed task N cell recv amount word
      positive (fun x u => chosen.site (back x) u) (task.lookupFrame 0) (D.directory pp lp).length origins
      progState siteID edgeID portID geom geometryInput original live reportHost hdr body factors slot)
    (cube : word=(packet).cube) (valid : declarationInRange word) (baseRoom : frame=arena.frame)
    (values : CubeConstants.valueBound task.id<2^w) (cubeRoom : task.cube.ReplayRoom w frame)
    (u : Fin (R+1)) (teamCount : task.cube.teams=R+1)
    (dest : dst u=arena.broadcastBase)
    (programs : Site.Programs N)
    (hidden : (c : Fin task.cube.cells) → Fin (externalBase N cell c (placedSize N programs)) → Bool)
    (gid : TableEntry task.cube.n task.cube.b task.cube.h task.cube.K task.cube.s → Fin task.p.report.gadgets)
    (ids : ∀ e,task.id e=(gid e).val)
    (r : ReceivedRows (fun _ : Fin task.cube.teams => report(frame,u)) task.cube.cells)
    (proposed : ∀ k, ReportAssignments (r.cells k))
    (axis : Fin (task.cube.n+1))
    (allocation : ReportAllocation task.before task.after (task.cube.cellWriter frame (ctl(u)) axis)
      (report(frame,u)) (r.cells (finCongr teamCount.symm u)) task.after.reportCursor)
    (marks : ∀ c ∈ r.cells (finCongr teamCount.symm u),
      ∀ b∈c.bundles, ∀ g∈b.positions, g.parameter<2^w ∧ g.place<w)
    (query guesses gates : ℕ)
    (addresses : task.FinishAddresses (arena) (ctl(u)) task.cube.header.profile task.cube.n task.cube.header.d
      task.cube.header.cap w w query guesses gates)
    (returned : ∃ cur descriptor, Nonempty (ReportArgumentCut (orig).reports
      (proposed (finCongr teamCount.symm u)) cur descriptor))
    {Orig : Type} (patch : ℕ → CellPacket.Placed Orig) (locations : ℕ → ℕ) (extras : ℕ → List CellSparse.Record)
    (roster : let parts := (ScheduleClock.argumentVisitsEquiv T.pub (install SparseExterior.driver n T.routines)
      (orig).reports.val.2.1 (orig).reports.val.2.2).symm (orig).arguments
      ∃ geometryInput : ScheduleClock.SparseCallInput T.pub parts.2.1.val.2.2,
        ScheduleClock.ProducedRoster task (task.controlRows u.val fr (tables(u)).ends (ctl(u)) (tables(u)).livePairs
          (D.teams*D.sites)) (readings parts.1.val.2.2) patch locations extras geometryInput)
    (cap : D.candidates ≤ task.cube.maxRows)
    (issued : (Arg → Word w) × List (TeamRAM.Event w) × RoutingISA.Bank w × Memory w)
    (identified : issued=F.sourceOwnedAt fixed source builders agree q reports u) :
    RegisteredOriginalPrefix (T.pub,(orig).owned.val) issued
      (OriginalPrefixRun task headerData gid (ownedBy(teamCount.symm)) (observedPath(programs,hidden)) frame (ctl(u))
      task.p.siteWidth task.p.bodyCap (fun _ => arena) r (finCongr teamCount.symm u) T pr proposed claim) := by
  subst issued
  refine ⟨fun matched => ?_⟩
  have registers : T.pub=(pub ∘ back) full.1 u := congrArg Prod.fst matched
  have atFrame : frame=fr := ((congrArg (fun z : Arg → Word w => (z 0).val) registers).trans
    (chosen.site (back full.1) u).origin).symm
  obtain ⟨cur,desc,observed⟩ := returned
  have allocation' := r.allocationAtFrame task (ctl(u)) task.p.siteWidth task.p.bodyCap atFrame
    (finCongr teamCount.symm u) (ctl(u)) axis allocation
  have marks' := r.marksAtFrame task (ctl(u)) task.p.siteWidth task.p.bodyCap atFrame (finCongr teamCount.symm u) marks
  have tape := r.cutAtLayout (frameCast(u,atFrame)) proposed (finCongr teamCount.symm u) (orig).reports observed.some
  have registration := PreparationFrame.SelectedLookupSites.registerOriginalPrefix G skeleton header task D pp lp
    pin guess dst ib hb sb frame receivingBase owner word pub mac reg mem host key sizes N cell recv amount positive
    wire same arena headerData claim previous origin fresh geomGates outputs field off ell literalCtl fixed F origins
    progState siteID edgeID portID geom geometryInput original live reportHost hdr body factors slot builders agree
    q reports T pr snap charge tail chosen reached cube valid baseRoom values cubeRoom u teamCount dest programs hidden
    gid ids atFrame r proposed axis allocation' marks' query guesses gates addresses tape patch locations extras roster cap
  exact registration.atSource matched

/-- On the physical processor frame, combine its allocated report rows and
marked positions with the registered tape returned on the original candidate
and the sparse patch produced on the very same argument invocation. -/
theorem PreparationFrame.SelectedLookupSites.issueSourcePrefixAtFrame
    {Trace : HeaderExterior skeleton header → Fin (R+1) → Type}
    (snap : ∀ x u, Trace x u → RoutingISA.Bank w × VPVNP.BurstRAM.Memory w)
    (charge : ∀ x u, Trace x u → ℕ × ℕ)
    (tail : ∀ (x : HeaderExterior skeleton header) (u : Fin (R+1)), atSite(x,u) → Trace x u → Prop)
    (chosen : F.SelectedLookupSites G skeleton header task D pp lp pin guess dst ib hb sb frame receivingBase
      owner word pub mac reg mem host key sizes N cell label recv amount wire same (fun x u site =>
        ∃ trace : Trace x u,
          site.OnReturn old(u) fresh geomGates outputs field off ell literalCtl (List.ofFn (packet).profile)
              (DiagonalTallyRAM.broadcast w (packet).rawCounts) 0 (snap x u trace).1 (snap x u trace).2
              (charge x u trace).1 (charge x u trace).2 ∧ tail x u site trace))
    (reached : F.CandidateReportsOnReplay (G:=G) (L:=wire) (header:=header) (pin:=pin) (d:=D) (pp:=pp) (lp:=lp)
      (pub:=pub ∘ back) (mac:=mac ∘ back) (reg:=reg ∘ back) (mem:=mem ∘ back)
      (initialBase:=frame) (receiving:=receivingBase) (pins:=fun j => PL j)
      (fields:=fun y j => G.processorFields j pin (back y).val (ib j) (hb j) (sb j))
      (bf:=fun j => BF j) (guess:=guess) (resides:=host) (key:=key) (sizes:=sizes)
      (representative:=owner) (group:=grp) (b:=b) (gap:=gap) (outputs:=outCount) fixed task N cell recv amount word
      positive (fun x u => chosen.site (back x) u) (task.lookupFrame 0) (D.directory pp lp).length origins
      progState siteID edgeID portID geom geometryInput original live reportHost hdr body factors slot)
    (cube : word=(packet).cube) (valid : declarationInRange word) (baseRoom : frame=arena.frame)
    (values : CubeConstants.valueBound task.id<2^w) (cubeRoom : task.cube.ReplayRoom w frame)
    (u : Fin (R+1)) (teamCount : task.cube.teams=R+1)
    (dest : dst u=arena.broadcastBase)
    (programs : Site.Programs N)
    (hidden : (c : Fin task.cube.cells) → Fin (externalBase N cell c (placedSize N programs)) → Bool)
    (gid : TableEntry task.cube.n task.cube.b task.cube.h task.cube.K task.cube.s → Fin task.p.report.gadgets)
    (ids : ∀ e,task.id e=(gid e).val)
    (atFrame : frame=fr) (r : ReceivedRows (fun _ : Fin task.cube.teams => report(frame,u)) task.cube.cells)
    (proposed : ∀ k, ReportAssignments (r.cells k))
    (axis : Fin (task.cube.n+1))
    (allocated :
      ReportAllocation task.before task.after (task.cube.cellWriter fr (ctl(u)) axis) (report(fr,u))
        ((r.atLayout (frameCast(u,atFrame))).cells (finCongr teamCount.symm u)) task.after.reportCursor ∧
      ∀ c ∈ (r.atLayout (frameCast(u,atFrame))).cells (finCongr teamCount.symm u),
        ∀ b∈c.bundles, ∀ g∈b.positions, g.parameter<2^w ∧ g.place<w)
    (query guesses gates : ℕ)
    (addresses : task.FinishAddresses (arena) (ctl(u)) task.cube.header.profile task.cube.n task.cube.header.d
      task.cube.header.cap w w query guesses gates)
    (returned : ∃ cur descriptor, Nonempty (ReportArgumentCut (orig).reports
      ((r.assignmentsAtLayout (frameCast(u,atFrame)) proposed) (finCongr teamCount.symm u)) cur descriptor))
    (roster : let parts := (ScheduleClock.argumentVisitsEquiv T.pub (install SparseExterior.driver n T.routines)
      (orig).reports.val.2.1 (orig).reports.val.2.2).symm (orig).arguments
      ∃ (Orig : Type) (patch : ℕ → CellPacket.Placed Orig) (locations : ℕ → ℕ) (extras : ℕ → List CellSparse.Record)
        (geometryInput : ScheduleClock.SparseCallInput T.pub parts.2.1.val.2.2),
        ScheduleClock.ProducedRoster task (task.controlRows u.val fr (tables(u)).ends (ctl(u)) (tables(u)).livePairs
          (D.teams*D.sites)) (readings parts.1.val.2.2) patch locations extras geometryInput)
    (cap : D.candidates ≤ task.cube.maxRows)
    (issued : (Arg → Word w) × List (TeamRAM.Event w) × RoutingISA.Bank w × Memory w)
    (identified : issued=F.sourceOwnedAt fixed source builders agree q reports u) :
    RegisteredOriginalPrefix (T.pub,(orig).owned.val) issued
      (OriginalPrefixRun task headerData gid (ownedBy(teamCount.symm)) (observedPath(programs,hidden)) frame (ctl(u))
      task.p.siteWidth task.p.bodyCap (fun _ => arena) r (finCongr teamCount.symm u) T pr proposed claim) := by
  obtain ⟨cur,desc,observed⟩ := returned
  obtain ⟨Orig,patch,locations,extras,built,produced⟩ := roster
  rw [identified]
  exact PreparationFrame.SelectedLookupSites.registerOriginalPrefix G skeleton header task D pp lp pin guess
    dst ib hb sb frame receivingBase owner word pub mac reg mem host key sizes N cell recv amount positive
    wire same arena headerData claim previous origin fresh geomGates outputs field off ell literalCtl fixed F
    origins progState siteID edgeID portID geom geometryInput original live reportHost hdr body factors slot
    builders agree q reports T pr snap charge tail chosen reached cube valid baseRoom values cubeRoom u teamCount
    dest programs hidden gid ids atFrame r proposed axis allocated.1 allocated.2 query guesses gates addresses
    observed.some patch locations extras ⟨built,produced⟩ cap

end TeamContraction

end BorderVNP
end Computability
end OAI

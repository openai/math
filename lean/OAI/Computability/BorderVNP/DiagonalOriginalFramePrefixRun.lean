import OAI.Computability.BorderVNP.DiagonalCandidateAtReturnedSource
import OAI.Computability.BorderVNP.DiagonalCandidateOriginalPrefixRun
import OAI.Computability.BorderVNP.DiagonalBootLookupOwnedHeader

/-! # The original selected signed finish from the admitted frame and its native return -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction
open Diagonal.ExternalSew.Fragments

open VPVNP BurstRAM MotifBase Diagonal.Layout Routing RoutingISA RoutingISA.Transmission RoutingISA.Evaluator
open _root_.OAI.Computability.BorderVNP.Cube Physical Tally MeanChoice GroupWeights LocalRow SignedPrep DiagonalTallyPacketEmit
open Crossing Packing.CellAddresses Packing.CellAddressCircuit Packing.CellAddressPhysical Packing.RoutingOutputs
open Packing.BottomReports DiagonalTallyCellReports DiagonalTallyAllocation ReportDirectory

variable {D w R X r teams pinsCount link inner n : ℕ} {Edge : Type} {G : Wiring R r teams pinsCount link inner n Edge}
    {L : WireLayout (R+1) r link} {header : List Bool} {pin : Fin pinsCount → Bool} (fixed : Block (R+1))
    (t : SignedTaskArena.Layout) {P A : Type} [Fintype P] [Fintype A] {bits : P → ℕ}
    (N : Network D P bits) (cell : N.Site → Fin t.cube.cells) (recv : A → Fin t.cube.cells) (size : A → ℕ)
    {d : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ}
    {pub : HeaderExterior L header → Fin (R+1) → Arg → Word w}
    {mac : HeaderExterior L header → Fin (R+1) → TeamOpcode.Macros w 8}
    {reg : HeaderExterior L header → Fin (R+1) → Bank w} {mem : HeaderExterior L header → Fin (R+1) → Memory w}
    {initialBase receiving : ℕ} {pins : Fin (R+1) → Pins.Layout}
    {fields : HeaderExterior L header → (u : Fin (R+1)) → Pins.ProcessorFields (pins u)}
    {bf : Fin (R+1) → BroadcastFrame} {guess : Fin (R+1) → ℕ → Bool} {I : Type*} [Fintype I]
    {resides : I → Fin t.cube.cells} {key : I ↪ ℕ} {sizes : I → ℕ}
    {representative : ℕ → Fin (R+1)} {group : Fin t.cube.header.d → Fin (R+1)}
    (raw : Broadcast t.cube.n t.cube.header.d t.cube.header.cap) (positive : 0<t.cube.header.d)
    (site : ∀ z u, CandidateSite (X:=X) t.cube d pp lp raw representative
      (Fin.ofNat (t.cube.n+1) (readCode (t.cube.n+1) raw.1),fun p j => readCode (t.cube.header.cap+1) (raw.2 p j))
      group initialBase receiving (pins u) (fields z u) (bf u) (guess u) (pub z u) (mac z u) (reg z u) (mem z u)
      resides key sizes N cell recv size)
    (F : PreparationFrame G L t.cube
      (Fin.ofNat (t.cube.n+1) (readCode (t.cube.n+1) raw.1),fun p j => readCode (t.cube.header.cap+1) (raw.2 p j))
      header pin pub mac reg mem)
    (template : Frame) (origin : Fin (R+1) → ℕ)
    {cb lb widthO outputs ns np : ℕ} {σ : Type} [Fintype σ] (state : N.Site → Packing.Inherited.Site)
    (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin t.cube.cables) (portID : P ↪ Fin np)
    (geom : Fields ns t.cube.cables np t.cube.cells cb lb widthO σ)
    (input : HeaderExterior L header → Fin (R+1) → σ → Bool)
    (original : Fin d.entries → N.Site) (live : Fin (d.teams*d.sites) → P)
    (host : Fin d.entries → Fin t.cube.cells) (hdr : Fin d.entries → BundleHeader)
    (body factors : Fin d.entries → List CellSparse.Factor) {b gap : ℕ}
    (slot : LiveBit N cell ↪ Slot t.cube.n t.cube.header.d t.cube.header.blocks (t.cube.h*t.cube.b))

local notation3 (prettyPrint := false) "decl" => Prod.mk (Fin.ofNat (t.cube.n+1) (readCode (t.cube.n+1) raw.1))
  (fun (p : Sym2 (Fin t.cube.header.d)) (j : Fin (t.cube.n+1)) => readCode (t.cube.header.cap+1) (raw.2 p j))
local notation3 (prettyPrint := false) "label" => meanPackedLabel N cell recv size (List.finRange t.cube.cells)
  t.cube.n t.cube.header.d positive
local notation3 (prettyPrint := false) "owns" => greedyOwner R t.cube.b t.cube.s label recv size
local notation3 (prettyPrint := false) "frozen" => fun j : Fin d.entries => physicalBundle (hdr j) (body j) (factors j) (fun _ => false)
local notation3 (prettyPrint := false) "ctl(" u ")" => controlsBase (origin u) t.cube.cables t.cube.cells d.entries (d.teams*d.sites)
local notation3 (prettyPrint := false) "report(" x "," u ")" => reportLayout t.before t.after x (ctl(u)) t.p.parameters t.p.siteWidth t.p.bodyCap t.cube.stop
local notation3 (prettyPrint := false) "source" => routedSourceReports t.cube N cell owns slot label
  (fun u => report(initialBase,u)) host frozen (fun c => suppliedSize N (fun v => (cell v).val) c)
  (fun c => guessedSize N (fun v => (cell v).val) c+siteSize N (fun v => (cell v).val) c (fun v => ((state v).size)))

variable (builders : F.Builders fixed t.id (greedyOwner R t.cube.b t.cube.s (meanPackedLabel N cell recv size (List.finRange t.cube.cells) t.cube.n t.cube.header.d positive) recv size)) (agree : F.SourceAgreement fixed (routedSourceReports t.cube N cell (greedyOwner R t.cube.b t.cube.s (meanPackedLabel N cell recv size (List.finRange t.cube.cells) t.cube.n t.cube.header.d positive) recv size) slot (meanPackedLabel N cell recv size (List.finRange t.cube.cells) t.cube.n t.cube.header.d positive)
    (fun u : Fin (R+1) => reportLayout t.before t.after initialBase (controlsBase (origin u) t.cube.cables t.cube.cells d.entries (d.teams*d.sites)) t.p.parameters t.p.siteWidth t.p.bodyCap t.cube.stop) host (fun j : Fin d.entries => physicalBundle (hdr j) (body j) (factors j) (fun _ => false))
    (fun c => suppliedSize N (fun v => (cell v).val) c) (fun c => guessedSize N (fun v => (cell v).val) c+siteSize N (fun v => (cell v).val) c (fun v => ((state v).size)))) builders)
  (q : {v : Declared t.cube (greedyOwner R t.cube.b t.cube.s (meanPackedLabel N cell recv size (List.finRange t.cube.cells) t.cube.n t.cube.header.d positive) recv size) (Prod.mk (Fin.ofNat (t.cube.n+1) (readCode (t.cube.n+1) raw.1)) (fun (p : Sym2 (Fin t.cube.header.d)) (j : Fin (t.cube.n+1)) => readCode (t.cube.header.cap+1) (raw.2 p j))) // (routedSourceReports t.cube N cell (greedyOwner R t.cube.b t.cube.s (meanPackedLabel N cell recv size (List.finRange t.cube.cells) t.cube.n t.cube.header.d positive) recv size) slot (meanPackedLabel N cell recv size (List.finRange t.cube.cells) t.cube.n t.cube.header.d positive)
    (fun u : Fin (R+1) => reportLayout t.before t.after initialBase (controlsBase (origin u) t.cube.cables t.cube.cells d.entries (d.teams*d.sites)) t.p.parameters t.p.siteWidth t.p.bodyCap t.cube.stop) host (fun j : Fin d.entries => physicalBundle (hdr j) (body j) (factors j) (fun _ => false))
    (fun c => suppliedSize N (fun v => (cell v).val) c) (fun c => guessedSize N (fun v => (cell v).val) c+siteSize N (fun v => (cell v).val) c (fun v => ((state v).size)))).pins v.val}) (reports : (routedSourceReports t.cube N cell (greedyOwner R t.cube.b t.cube.s (meanPackedLabel N cell recv size (List.finRange t.cube.cells) t.cube.n t.cube.header.d positive) recv size) slot (meanPackedLabel N cell recv size (List.finRange t.cube.cells) t.cube.n t.cube.header.d positive)
    (fun u : Fin (R+1) => reportLayout t.before t.after initialBase (controlsBase (origin u) t.cube.cables t.cube.cells d.entries (d.teams*d.sites)) t.p.parameters t.p.siteWidth t.p.bodyCap t.cube.stop) host (fun j : Fin d.entries => physicalBundle (hdr j) (body j) (factors j) (fun _ => false))
    (fun c => suppliedSize N (fun v => (cell v).val) c) (fun c => guessedSize N (fun v => (cell v).val) c+siteSize N (fun v => (cell v).val) c (fun v => ((state v).size)))).actual q.val.val)
  (publication : F.LookupPublication t)
local notation3 (prettyPrint := false) "slots" =>
  (publication.directory.directory publication.privatePlacement publication.livePlacement).length+t.cube.header.d.choose 2
local notation3 (prettyPrint := false) "operands" => declaredWords t.cube owns decl q.val
local notation3 (prettyPrint := false) "replayZ" => F.replay fixed operands
local notation3 (prettyPrint := false) "full" => (F.sourceEquiv fixed source builders agree).symm ⟨q,reports⟩
local notation3 (prettyPrint := false) "vis" => fun u => (visitsEquiv t.id (pub full.1 u) (mac full.1 u)
  (reg full.1 u) (mem full.1 u)).symm (full.2 u)
local notation3 (prettyPrint := false) "scan" => visitedOwnedScans (ar:=t.cube) vis

set_option maxHeartbeats 2200000
set_option maxRecDepth 8500
set_option autoImplicit false


open RoutingISA.CompactMachine CellMacro.Generator ProcessorSlots JointHeader Physical.NativeLedger
open FiniteEvaluator Physical.NativeAssignments SignedTaskArena Packing.Inherited Packing.Inherited.Placement

variable (T : PositiveTeam t.id SparseExterior.driver n w) (pr : T.Prefix)
local notation3 (prettyPrint := false) "orig" => prefixVisits T pr
local notation3 (prettyPrint := false) "fr" => (T.pub 0).val
local notation3 (prettyPrint := false) "tables(" u ")" => bases (origin u) t.cube.cables t.cube.cells d.entries
local notation3 (prettyPrint := false) "frameCast(" u "," h ")" => congrArg (fun v => report(v,u)) h
local notation3 (prettyPrint := false) "ownedBy(" eqn ")" => (finCongr eqn) ∘ owns q.val.val.1
local notation3 (prettyPrint := false) "observedPath(" programs "," hidden ")" => rawPath N cell edgeID programs owns q.val.val hidden

private theorem mappedNumber {a b : ℕ} (h : a=b) (i : Fin a) : ((finCongr h) i).val=i.val := by
  subst b
  rfl

/-- Continue this declared source with its genuine owned register state, the
real candidate report writer, the original boot's lookup arrays, and the
actual emitted sparse roster. This gives exactly the original-prefix input
to the outer canonical-proposal elimination. -/
theorem PreparationFrame.sourceEquiv_originalPrefixRunOnOwned
    (reached : F.CandidateReportsOnReplay (b:=b) (gap:=gap) (outputs:=outputs) fixed t N cell recv size raw positive site template
      (publication.directory.directory publication.privatePlacement publication.livePlacement).length origin
      state siteID edgeID portID geom input original live host hdr body factors slot)
    (common : ∀ u,readings (pub replayZ.1 u) 0=publication.frame)
    (room : t.after.packed ≤ 2^w) (values : CubeConstants.valueBound t.id<2^w)
    (space : t.cube.ReplayRoom w publication.frame)
    (scanner : ∀ u : Fin (R+1),t.cube.ScannerWords (readings (pub replayZ.1 u) 0) u.val (decl).1.val
      (fun j => (F.group j).val) (readings (pub replayZ.1 u)) (F.source replayZ.1 u) (decl).2)
    (constant : ∀ u,CubeConstants.Fields
      (CubeConstants.inArena template t.cube.stop t.cube.n t.cube.b t.cube.h t.cube.K t.cube.s)
      (readings (pub replayZ.1 u) 0) (CubeConstants.idBase t.cube.stop t.cube.n t.cube.b t.cube.h t.cube.K t.cube.s)
      (F.source replayZ.1 u))
    (scheduled : F.group=owns q.val.val.1)
    (u : Fin (R+1)) (teamCount : t.cube.teams=R+1)
    (same : (T.pub,(orig).owned.val)=(pub full.1 u,((vis) u).owned.val))
    (programs : Site.Programs N)
    (hidden : (c : Fin t.cube.cells) → Fin (externalBase N cell c (placedSize N programs)) → Bool)
    (gid : TableEntry t.cube.n t.cube.b t.cube.h t.cube.K t.cube.s → Fin t.p.report.gadgets)
    (ids : ∀ e,t.id e=(gid e).val)
    (fEq : initialBase=fr) (r : ReceivedRows (fun _ : Fin t.cube.teams => report(initialBase,u)) t.cube.cells)
    (proposed : ∀ k, ReportAssignments (r.cells k))
    (startup : Fin t.cube.teams → StartupArena)
    (hdr₀ : PositiveFields t.cube.header.profile t.cube.n t.cube.header.d t.cube.header.cap t.cube.teams t.dim w)
    (cc : Fin (t.cube.teams*t.dim*w) → Bool)
    (installed : (pub replayZ.1 u 0).val=(startup (finCongr teamCount.symm u)).frame)
    (sourceDeck : CubePacket.WordPrepared (gadgetLookup t (pub full.1 u)
      (Fin.valEmbedding ∘ owns q.val.val.1) u.val D
      (Scatter.Assignment.bankData q.val.val.2 t.cube.header.packetBase t.cube.singleBank))
      t.id (pub full.1 u) ((vis) u).owned.val.2.2)
    (sourceHeader : HeaderSeed t (hdr₀.withSubtotals cc) (pub full.1 u)
      (rawAddress (startup (finCongr teamCount.symm u)) t.cube.header.profile t.cube.n t.cube.header.d t.cube.header.cap)
      u.val ((vis) u).owned.val.2.2)
    (axis : Fin (t.cube.n+1))
    (allocation : ReportAllocation t.before t.after (t.cube.cellWriter fr (ctl(u)) axis)
      (report(fr,u)) (((r.atLayout (frameCast(u,fEq))).cells (finCongr teamCount.symm u))) t.after.reportCursor)
    (marks : ∀ c ∈ (r.atLayout (frameCast(u,fEq))).cells (finCongr teamCount.symm u),
      ∀ b∈c.bundles, ∀ g∈b.positions, g.parameter<2^w ∧ g.place<w)
    (query guesses gates : ℕ)
    (addresses : t.FinishAddresses (startup (finCongr teamCount.symm u)) (ctl(u)) t.cube.header.profile t.cube.n t.cube.header.d
      t.cube.header.cap w w query guesses gates)
    {cur : ReportCursor} {descriptor : ℕ}
    (observed : ReportArgumentCut (orig).reports (r.assignmentsAtLayout (frameCast(u,fEq)) proposed
      (finCongr teamCount.symm u)) cur descriptor)
    {Orig : Type} (patch : ℕ → CellPacket.Placed Orig) (locations : ℕ → ℕ) (extras : ℕ → List CellSparse.Record)
    (roster : let parts := (ScheduleClock.argumentVisitsEquiv T.pub (install SparseExterior.driver n T.routines)
      (orig).reports.val.2.1 (orig).reports.val.2.2).symm (orig).arguments
      ∃ input : ScheduleClock.SparseCallInput T.pub parts.2.1.val.2.2,
        ScheduleClock.ProducedRoster t (t.controlRows u.val fr (tables(u)).ends (ctl(u)) (tables(u)).livePairs
          (d.teams*d.sites)) (readings parts.1.val.2.2) patch locations extras input)
    (cap : d.candidates ≤ t.cube.maxRows) :
    OriginalPrefixRun t hdr₀ gid (ownedBy(teamCount.symm)) (observedPath(programs,hidden)) initialBase (ctl(u))
      t.p.siteWidth t.p.bodyCap startup r (finCongr teamCount.symm u) T pr proposed cc := by
  obtain ⟨bank,digits,⟨actual⟩⟩ := F.sourceEquiv_returnedCandidate fixed t N cell recv size raw positive site template
    origin state siteID edgeID portID geom input original live host hdr body factors slot builders agree q reports
    publication reached common room values space scanner constant scheduled
  have samePub : T.pub=pub full.1 u := congrArg Prod.fst same
  have currentFrame : ((scan).pub u 0).val=fr := (congrArg (fun p => (p 0).val) samePub).symm
  have sameMem := (congrArg (fun p => p.2.2.2) same).symm
  have number := mappedNumber teamCount.symm u
  have nuOwner : Fin.val ∘ (ownedBy(teamCount.symm))=Fin.valEmbedding ∘ owns q.val.val.1 :=
    funext fun j => mappedNumber teamCount.symm (owns q.val.val.1 j)
  let data := Scatter.Assignment.bankData q.val.val.2 t.cube.header.packetBase t.cube.singleBank
  let readsDeck (p : (Arg → Word w) × Memory w) :=
    CubePacket.WordPrepared (gadgetLookup t p.1 (Fin.valEmbedding ∘ owns q.val.val.1) u.val D data)
      t.id p.1 p.2
  have transfer := congrArg (fun z => (z.1,z.2.2.2)) same
  have deck := (congrArg readsDeck transfer).mpr sourceDeck
  let namedHeader (p : (Arg → Word w) × Memory w) := HeaderSeed t (hdr₀.withSubtotals cc) p.1
    (rawAddress (startup (finCongr teamCount.symm u)) t.cube.header.profile t.cube.n t.cube.header.d t.cube.header.cap)
    (finCongr teamCount.symm u).val p.2
  have originalHeader : namedHeader (pub full.1 u,((vis) u).owned.val.2.2) := by
    dsimp only [namedHeader]
    rw [number]
    exact sourceHeader
  have copied := (congrArg namedHeader transfer).mpr originalHeader
  have extEq : full.1=replayZ.1 := Subtype.ext rfl
  have installedFrame : fr=(startup (finCongr teamCount.symm u)).frame :=
    currentFrame.symm.trans ((congrArg (fun ex => (pub ex u 0).val) extEq).trans
      installed)
  apply actual.originalPrefixRun N t cell recv size raw (site full.1) origin state siteID edgeID portID geom
    original live host hdr body factors bank slot digits T pr u (finCongr teamCount.symm u) number
    currentFrame sameMem cap gid (ownedBy(teamCount.symm)) (observedPath(programs,hidden)) initialBase fEq r
    proposed startup hdr₀ cc installedFrame copied ?_ axis allocation marks query guesses gates addresses
    observed patch locations extras ?_ ids
  · rw [rawPath_banks,number,nuOwner]
    exact deck
  · simpa only [number] using roster

/-- Recover both immutable inputs from the same selected boot and continue the original prefix. -/
theorem PreparationFrame.sourceEquiv_originalPrefixRun
    (reached : F.CandidateReportsOnReplay (b:=b) (gap:=gap) (outputs:=outputs) fixed t N cell recv size raw positive site template
      (publication.directory.directory publication.privatePlacement publication.livePlacement).length origin
      state siteID edgeID portID geom input original live host hdr body factors slot)
    (common : ∀ u,readings (pub replayZ.1 u) 0=publication.frame)
    (room : t.after.packed ≤ 2^w) (values : CubeConstants.valueBound t.id<2^w)
    (space : t.cube.ReplayRoom w publication.frame)
    (scanner : ∀ u : Fin (R+1),t.cube.ScannerWords (readings (pub replayZ.1 u) 0) u.val (decl).1.val
      (fun j => (F.group j).val) (readings (pub replayZ.1 u)) (F.source replayZ.1 u) (decl).2)
    (constant : ∀ u,CubeConstants.Fields
      (CubeConstants.inArena template t.cube.stop t.cube.n t.cube.b t.cube.h t.cube.K t.cube.s)
      (readings (pub replayZ.1 u) 0) (CubeConstants.idBase t.cube.stop t.cube.n t.cube.b t.cube.h t.cube.K t.cube.s)
      (F.source replayZ.1 u))
    (scheduled : F.group=owns q.val.val.1)
    (u : Fin (R+1)) (teamCount : t.cube.teams=R+1)
    (same : (T.pub,(orig).owned.val)=(pub full.1 u,((vis) u).owned.val))
    (boot : F.BootLookupAt t fixed source builders q u)
    (programs : Site.Programs N)
    (hidden : (c : Fin t.cube.cells) → Fin (externalBase N cell c (placedSize N programs)) → Bool)
    (gid : TableEntry t.cube.n t.cube.b t.cube.h t.cube.K t.cube.s → Fin t.p.report.gadgets)
    (ids : ∀ e,t.id e=(gid e).val)
    (fEq : initialBase=fr) (r : ReceivedRows (fun _ : Fin t.cube.teams => report(initialBase,u)) t.cube.cells)
    (proposed : ∀ k, ReportAssignments (r.cells k))
    (startup : Fin t.cube.teams → StartupArena)
    (hdr₀ : PositiveFields t.cube.header.profile t.cube.n t.cube.header.d t.cube.header.cap t.cube.teams t.dim w)
    (cc : Fin (t.cube.teams*t.dim*w) → Bool)
    (sameArena : boot.arena=startup (finCongr teamCount.symm u))
    (headerBits : (hdr₀.withSubtotals cc).bits=header)
    (sendAt : (boot.args u).dst=boot.arena.broadcastBase)
    (axis : Fin (t.cube.n+1))
    (allocation : ReportAllocation t.before t.after (t.cube.cellWriter fr (ctl(u)) axis)
      (report(fr,u)) (((r.atLayout (frameCast(u,fEq))).cells (finCongr teamCount.symm u))) t.after.reportCursor)
    (marks : ∀ c ∈ (r.atLayout (frameCast(u,fEq))).cells (finCongr teamCount.symm u),
      ∀ b∈c.bundles, ∀ g∈b.positions, g.parameter<2^w ∧ g.place<w)
    (query guesses gates : ℕ)
    (addresses : t.FinishAddresses (startup (finCongr teamCount.symm u)) (ctl(u)) t.cube.header.profile t.cube.n t.cube.header.d
      t.cube.header.cap w w query guesses gates)
    {cur : ReportCursor} {descriptor : ℕ}
    (observed : ReportArgumentCut (orig).reports (r.assignmentsAtLayout (frameCast(u,fEq)) proposed
      (finCongr teamCount.symm u)) cur descriptor)
    {Orig : Type} (patch : ℕ → CellPacket.Placed Orig) (locations : ℕ → ℕ) (extras : ℕ → List CellSparse.Record)
    (roster : let parts := (ScheduleClock.argumentVisitsEquiv T.pub (install SparseExterior.driver n T.routines)
      (orig).reports.val.2.1 (orig).reports.val.2.2).symm (orig).arguments
      ∃ input : ScheduleClock.SparseCallInput T.pub parts.2.1.val.2.2,
        ScheduleClock.ProducedRoster t (t.controlRows u.val fr (tables(u)).ends (ctl(u)) (tables(u)).livePairs
          (d.teams*d.sites)) (readings parts.1.val.2.2) patch locations extras input)
    (cap : d.candidates ≤ t.cube.maxRows) :
    OriginalPrefixRun t hdr₀ gid (ownedBy(teamCount.symm)) (observedPath(programs,hidden)) initialBase (ctl(u))
      t.p.siteWidth t.p.bodyCap startup r (finCongr teamCount.symm u) T pr proposed cc := by
  have sourceDeck := boot.prepared t fixed source F builders agree q reports D
  have rawHeader := boot.ownedHeader t fixed source F builders agree q reports (hdr₀.withSubtotals cc)
    (headerBits.trans (replayZ.1.property fixed).symm) sendAt
    ((congrArg StartupArena.header sameArena).trans addresses.headerSize) teamCount
    (teamCount ▸ addresses.teamsFit) addresses.wordPos addresses.endFit
  apply F.sourceEquiv_originalPrefixRunOnOwned fixed t N cell recv size raw positive site template origin state
    siteID edgeID portID geom input original live host hdr body factors slot builders agree q reports publication
    T pr reached common room values space scanner constant scheduled u teamCount same programs hidden gid ids fEq
    r proposed startup hdr₀ cc (boot.head.trans (congrArg StartupArena.frame sameArena)) sourceDeck ?_ axis allocation
    marks query guesses gates addresses observed patch locations extras roster cap
  rw [←sameArena]
  exact rawHeader

end TeamContraction

end BorderVNP
end Computability
end OAI

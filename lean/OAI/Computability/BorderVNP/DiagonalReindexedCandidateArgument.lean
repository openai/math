import OAI.Computability.BorderVNP.DiagonalCandidateIssuedArgument

/-! # The registered argument window on an equal planner layout -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Transmission Routing PackedHistoryCircuit
open BorderVNP.Cube Cube.Physical Cube.Scatter Cube.TeamRows Scatter.Assignment DiagonalTallyPacketEmit
open FiniteEvaluator Evaluator SignedPrep Packing RoutingOutputs Crossing CellAddresses CellAddressCircuit
open Packing.Directory CellAddressPhysical Cube.MeanChoice Cube.LabelIndex Cube.NativeIntervals Cube.HostScatter
open TeamContraction.JointHeader CubeHeaderInstall LocalRow Physical.NativeAssignments
open Diagonal.ExternalSew.Fragments
open RoutingISA.Evaluator.ScheduleClock FiniteEvaluator.OpenSuffix DiagonalTallyCellReports CellMacro.Generator CellDispatch
open ProcessorSlots RoutingISA.CompactMachine
open scoped Classical
set_option maxHeartbeats 4200000
set_option maxRecDepth 5500

variable {R r t pins₀ link inner e₀ w : ℕ} {Edge : Type} {G : Wiring R r t pins₀ link inner e₀ Edge}
variable {pin : Fin pins₀ → Bool} {ext : Exterior R r link → Bool} {L : WireLayout (R+1) r link}
variable (u : Fin (R+1))
variable {D s n d k b : ℕ} {P σ : Type} [Fintype P] [Fintype σ] {bits : P → ℕ}
    {physical task : SignedTaskArena.Layout} (same : physical=task) (dir : Directory.Layout) (N : Network D P bits) (cell : N.Site → Fin physical.cube.cells)
    (aux : N.Site → ℕ) (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin physical.cube.cables) (portID : P ↪ Fin n)
    (F : Fields s physical.cube.cables n physical.cube.cells d k b σ) (x : σ → Bool)
    (net : Represents N cell aux siteID edgeID portID F x) (ids : ∀ c,(F.cells c).val=c.val)
    (wireFit : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^b)
    (hk : k ≤ b) (wordFit : b ≤ w) (positive : 0<physical.cube.cells)
    (original : Fin dir.entries ↪ N.Site) (live : (Fin dir.teams × Fin dir.sites) ↪ P)
    (liveWidth : ∀ j,bits (live j)=dir.block) (bounds : dir.DestinationBounds)
    (origin gap : ℕ)

variable (U : Fin (R+1) → PinStart SparseExterior.driver e₀ w) (active : PinStart.JointPrefix task.id U)
variable {decl : LengthDeclaration task.cube.n task.cube.header.d} {template : DiagonalTallyPacketEmit.Frame}
    {count : ℕ} {common : List Bool} {publicAt : HeaderExterior L common → Fin (R+1) → Arg → Word w}
    {macroAt : HeaderExterior L common → Fin (R+1) → TeamOpcode.Macros w 8}
    {regAt : HeaderExterior L common → Fin (R+1) → Bank w}
    {memAt : HeaderExterior L common → Fin (R+1) → Memory w}
    (frame : PreparationFrame G L task.cube decl common pin publicAt macroAt regAt memAt)
    (seen : HeaderExterior L common) (alphabet : 0<physical.cube.header.d)

variable {X packetDim bankDim : ℕ} {word : Broadcast task.cube.n task.cube.header.d task.cube.header.cap}
    {owner : ℕ → Fin (R+1)} {group : Fin task.cube.header.d → Fin (R+1)} {guess : ℕ → Bool}
    (a : StartupArena) (slotTeam : Fin a.teams) (slot : ℕ) (packet : ReferencePacket w packetDim)
    (bf : BroadcastFrame) (hdr : List Bool) (fields : Pins.ProcessorFields (a.operands slotTeam slot packet).layout)
    (bitsAt : Fin bankDim → Bool) {postPin : Bank w} {pinMem : Memory w}
    {sourcePub : Arg → Word w} {sourceMac : TeamOpcode.Macros w 8}
    {I A : Type} [Fintype I] {host : I → Fin task.cube.cells} {keys : I ↪ ℕ} {sizes : I → ℕ}
    {dest : A → Fin task.cube.cells} {amount : A → ℕ}
    (site : CandidateSite (X:=X) task.cube dir (NativeDemands.privatePair N cell edgeID portID dir original live gap)
      (NativeDemands.livePair N cell edgeID portID dir original live gap) word owner decl group a.frame a.next
      (a.operands slotTeam slot packet).layout fields bf guess sourcePub sourceMac
      postPin pinMem host keys sizes N (cast (congrArg (fun t : SignedTaskArena.Layout => N.Site → Fin t.cube.cells) same) cell) dest amount)

local notation3 (prettyPrint := false) "pub" => (U u).pub
local notation3 (prettyPrint := false) "head" => (pub 0).val
local notation3 (prettyPrint := false) "mac" => CompactMachine.install SparseExterior.driver e₀ (U u).routines
local notation3 (prettyPrint := false) "pr" => privateLayout head origin task.cube.cables task.cube.cells dir.entries dir.description gap
local notation3 (prettyPrint := false) "tabs" => bases origin physical.cube.cables physical.cube.cells dir.entries
local notation3 (prettyPrint := false) "pp" => ISA.placement (readings site.middle) (pr).raw
local notation3 (prettyPrint := false) "lp" => ISA.placement (readings site.middle) (tabs).livePairs
local notation3 (prettyPrint := false) "list" => NativeDemands.rows N cell edgeID portID dir original live gap
local notation3 (prettyPrint := false) "recv" => NativeDemands.receiver N cell edgeID portID dir original live gap bounds
local notation3 (prettyPrint := false) "width₀" => fun i : Fin (list).length => list[i.val].width
local notation3 (prettyPrint := false) "physicalLab" => meanPackedLabel N cell recv width₀ (List.finRange physical.cube.cells)
  physical.cube.n physical.cube.header.d alphabet
local notation3 (prettyPrint := false) "lab" => cast (congrArg (fun t : SignedTaskArena.Layout =>
  Fin t.cube.cells → Cube.Label (t.cube.n+1) t.cube.header.d) same) physicalLab
local notation3 (prettyPrint := false) "actualRecv" => cast (congrArg (fun t : SignedTaskArena.Layout =>
  Fin (list).length → Fin t.cube.cells) same) recv
local notation3 (prettyPrint := false) "who" => greedyOwner (blocks:=physical.cube.header.blocks) (K:=physical.cube.K) (h:=physical.cube.h) R physical.cube.b physical.cube.s physicalLab recv width₀
local notation3 (prettyPrint := false) "v" => PinStart.visits task.id U (active u)
local notation3 (prettyPrint := false) "afterArg" => (v).reports.val.2.2
local notation3 (prettyPrint := false) "parts" => (argumentVisitsEquiv pub mac (v).reports.val.2.1 afterArg).symm (v).arguments

open RoutingISA.CompactMachine

include net ids wireFit hk wordFit positive liveWidth in
/-- Transport one complete issued window along equality of the planner and published
layouts. The native packet, raw placement arrays, and routed assignment stay in
their original numbering. The returned site uses its installed layout's cardinalities. -/
theorem PreparationFrame.ReturnedOwnershipAt.reindexed_candidate_argument
    (publication : PublishedPin task dir N
      (cast (congrArg (fun t : CubeArena.Layout => N.Site → Fin t.cells) (congrArg SignedTaskArena.Layout.cube same)) cell)
      (cast (congrArg (fun t : CubeArena.Layout => N.Edge ↪ Fin t.cables) (congrArg SignedTaskArena.Layout.cube same)) edgeID)
      portID original live a slotTeam slot packet origin gap bf hdr
      fields sourcePub sourceMac bitsAt postPin pinMem site.geometryRegs site.geometry site.used site.profileCost)
    (pubAt : sourcePub=pub) (macAt : sourceMac=mac)
    (image : Image F (siteID ∘ original) (portID ∘ live ∘ finProdFinEquiv.symm) x origin (readings site.geometry))
    (header : Header head origin task.cube.cables task.cube.cells dir.entries (readings site.geometry))
    (scratch : a.next+7*dir.candidates≤origin) (originFit : origin<2^w)
    (teams : dir.teams≤2^w) (processors : dir.processors≤2^w) (fieldCount : dir.fields≤2^w)
    (literal : dir.literal<2^w) (cells : task.cube.cells≤2^w) (stride : task.cube.cellStride≤2^w)
    (below : origin+3*task.cube.cables≤task.cube.header.header)
    (source : frame.source seen u=readings site.receipt.history.sharedInput)
    (decoded : (Fin.ofNat (task.cube.n+1) (readCode (task.cube.n+1) word.1),
      fun pair j => readCode (task.cube.header.cap+1) (word.2 pair j))=decl)
    (templateFit : LocalRow.templateLimit task.cube.n task.cube.b task.cube.h task.cube.K task.cube.s<2^w)
    (team : bf.team=u.val)
    (cap : ∀ pair, load (cablePair (NativeDemands.cableOrder N cell edgeID) (crossSrc N cell) (crossDst N cell) physicalLab)
      (crossWidth N cell ∘ (NativeDemands.cableOrder N cell edgeID).symm) pair ≤ physical.cube.header.blocks*(physical.cube.h*physical.cube.b))
    {routeOwner : (Cube.Packet task.cube.n task.cube.header.d task.cube.header.blocks →
      Cube.Selector task.cube.n task.cube.K task.cube.h) → Fin task.cube.header.d → Fin (R+1)}
    (ownerCoordinates : HEq routeOwner who)
    (q : NativeAssignments.Routed (b:=task.cube.b) (s:=task.cube.s) routeOwner)
    (returned : frame.ReturnedOwnershipAt task seen ext template count q (PinStart.ownedVisits (ar:=task.cube) U active))
    (control : ℕ) (controlAt : site.control=control)
    (packetBits p d₁ J parameters expBits budget : ℕ)
    (box : Fin dir.entries → Fin task.cube.cells) (body : Fin dir.entries → BottomReports.BundleHeader)
    (Kpos : 1≤task.cube.K) (wpos : 0<w) (desc : 1≤dir.description)
    (ready : Ready (task.openInputs u.val head (tabs).ends control (tabs).livePairs
      (dir.teams*dir.sites) dir.entries packetBits box body) head (readings (v).owned.val.2.2) w)
    (reported : IssuedReportFrame task pub afterArg (tabs).ends control (list).length)
    {fragmentFit : (FragmentRows.Layout.fromFrame head (readings afterArg)).Fits w (readings afterArg)}
    {fragmentCells : task.fragments.cells=(FragmentRows.Layout.fromFrame head (readings afterArg)).cells}
    (emission : FragmentRows.SparseEmission task (FragmentRows.Layout.fromFrame head (readings afterArg)) afterArg fragmentFit fragmentCells)
    (bank : emission.output=(parts).1.val.2.2)
    (rate : ∀ pp' lp' (frameAddr axis : ℕ) (after : ℕ → ℕ), let geometry := LabelIndex.layout frameAddr after
      geometry.cells=task.cube.cells → geometry.cableCount=task.cube.cables →
      geometry.deliveryCount=(dir.directory pp' lp').length → geometry.labels=task.cube.alphabet →
      (CubeConstants.install task.id).slots+argumentDirectory task.cube.cells dir.entries+
        32*descriptorTicks geometry after (task.cube.alphabet-1) (task.cube.n+1)
          (weightLayout task.cube frameAddr axis) (teamLayout task.cube R)+
        (82*geometry.cableCount+cubeCoefficient task.cube.n task.cube.b task.cube.h task.cube.K task.cube.s
          (Cube.Tally.argumentWidth task.cube.n task.cube.b task.cube.h task.cube.K task.cube.s)*(task.cube.alphabet^2+X+1))+
        cellWork w (2^p+2^d₁) (J*(parameters*expBits)) X ≤ budget) :
    ∃ (z : Returns (.seq LabelIndex.directoryProgram NativeIntervals.prepare) pub mac
        site.published.val.2.1 site.published.val.2.2) (assigned : ℕ → ℕ),
      let prof := powerHeaderImage task.cube bf.dst (readings z.val.2.2)
      CubeArena.DirectoryImage task.cube head control decl.1 R prof assigned (readings site.receipt.history.dataInput) ∧
      ∃ win : PinStart.PublishedArgumentWindow task task.id U (u:=u) (active u) decl lab actualRecv width₀ X dir.description p d₁
        J parameters expBits (FragmentRows.Layout.fromFrame head (readings afterArg))
        (task.openInputs u.val head (tabs).ends control (tabs).livePairs (dir.teams*dir.sites) dir.entries packetBits box body).control
        (readings emission.output) budget, win.profile=prof ∧ win.assigned=assigned := by
  subst control
  subst sourcePub
  subst sourceMac
  subst task
  have ownerEq := eq_of_heq ownerCoordinates
  subst routeOwner
  exact PreparationFrame.ReturnedOwnershipAt.candidate_issued_argument u dir N cell aux siteID edgeID portID F x
    net ids wireFit hk wordFit positive original live liveWidth bounds origin gap U active frame seen alphabet
    a slotTeam slot packet bf hdr fields bitsAt site publication image header scratch originFit teams processors
    fieldCount literal cells stride below source decoded templateFit team cap q returned packetBits p d₁ J parameters expBits
    budget box body Kpos wpos desc ready reported emission bank rate

end TeamContraction

end BorderVNP
end Computability
end OAI

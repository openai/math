import OAI.Computability.BorderVNP.DiagonalOneReportSourceWords
import OAI.Computability.BorderVNP.DiagonalSelectedHostSource
import OAI.Computability.BorderVNP.DiagonalSelectedIssuedOwnerTables
import OAI.Computability.BorderVNP.DiagonalSelectedIssuedSaved
import OAI.Computability.BorderVNP.DiagonalReportSourceChart
import OAI.Computability.BorderVNP.DiagonalCanonicalFragmentPlacements
import OAI.Computability.BorderVNP.DiagonalSelectedReportSourceSlots
import OAI.Computability.BorderVNP.DiagonalSignedWriterReceipt
import OAI.Computability.BorderVNP.PackedFinalReportTemplate

/-! # A physical report for one team on the selected wired history -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity
open Packing Packing.Inherited Packing.DeckGrid Packing.PhysicalEpochs Diagonal Diagonal.CellEntries
open Diagonal.ExternalSew Diagonal.ExternalSew.RowTrace TeamContraction ParseBatch ParseBatchVerifier Prewire VPVNP
open VPVNP.ParseGrammar EnrichedOuter TeamScales BorderVNP.Cube.Physical.NativeAssignments
open scoped Classical BigOperators BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 3200000
set_option maxRecDepth 7200
set_option synthInstance.maxSize 4000

variable {D m : ℕ} [NeZero D] {K Gadget : Type} [Field K] {e : PaidIdentity K D m} {S : SiteSchedule e}
    {R r pins link k d a regs rw ec width s copies T header work : ℕ}
    (plan : SeedPlan S (k+1) r d T copies header work)
    (p : UniversalMachine.Program)
    (fit : 2*((UniversalMachine.programPrefix p).length+(TeamContraction.cutWidth (k+1)+a))+
      R*link+Wires.innerWidth r regs rw ec width ≤ k+1)
local notation3 (prettyPrint := false) "axes" => Fintype.card (Cube D)
local notation3 (prettyPrint := false) "tiles" => GridHosts.tileCount (Fintype.card (Cube D)) d
local notation3 (prettyPrint := false) "G₀" => tapeTemplate p fit pins
variable {order : Fin (GridHosts.tileCount (Fintype.card (Cube D)) d) ≃ (Fin (Fintype.card (Cube D)) → Deck (d+2))}
    (W : WiredWitness (tapeTemplate p fit pins) (Fin.last k) D (Fintype.card (Cube D)) d order
      (0 : ParseTable.State (Fin (k+1) × Bool) s))
    (position : (Fin (Fintype.card (Cube D)) → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (code : PairedParameters k s ↪ ℕ) {ns ne np : ℕ}
    (sites : (W.routedFine position).Site ↪ Fin ns) (edges : (W.routedFine position).Edge ↪ Fin ne)
    (ports : Fin r × Fin (publicWidth (tapeTemplate p fit pins)) ↪ Fin np)
    (table : (seedBundle (tapeTemplate p fit pins) (Fintype.card (Cube D)) d order position copies).Tables K)
local notation3 (prettyPrint := false) "C" => plan.compiled
local notation3 (prettyPrint := false) "mass" => initialMass (D:=D) (k+1) r d copies header
local notation3 (prettyPrint := false) "budget" => boundaryBudget S mass
local notation3 (prettyPrint := false) "word₀" => 60*logWidth r (k+1)
local notation3 (prettyPrint := false) "seedBlock" => GridHosts.inputBlockWidth r (k+1) axes d
local notation3 (prettyPrint := false) "seedCap" => seedBoxCapacity (k+1) r axes d (Fintype.card (Direction axes))
local notation3 (prettyPrint := false) "desc" => seedDescriptionWidth (k+1) r axes d (header*logWidth r (k+1)) (BottomGridBank.bodyBudget seedCap)

variable (words : Boundary.Pins S (d+1) (boundary S (d+1)) (60*logWidth r (k+1)) 0 → Bool)
    (good : Boundary.Good (boundaryBudget S (initialMass (D:=D) (k+1) r d copies header)) 0 (Boundary.seedState S (tapeTemplate p fit pins) d order position copies table words))
    (seeds : ∀ h, ∀ i : Fin S.rounds,
      ((Cube D → Deck (S.level (offset S (d+1) h) (i.val+1)+1)) × (S.source.pattern i).bins.Bin) → ℕ)
    (free : Fin (R+1) → Fin r → Fin a → Bool) (count : (fan S)^T*copies = R+1)
    (pos : e.Entry → Gadget) (num : Gadget ↪ ℕ)
local notation3 (prettyPrint := false) "goodState" => Boundary.Good (S := S) (start := d+1) (P := Fin tiles)
  (bits := fun _ => copies*GridHosts.inputBlockWidth r (k+1) axes d)
  (shape := boundary S (d+1)) (w := word₀) budget
local notation3 (prettyPrint := false) "leaf" => (Subtype.mk (Boundary.seedState S G₀ d order position copies table words) good : Admissible goodState 0)
local notation3 (prettyPrint := false) "key" => Equiv.toEmbedding (finCongr (seedPortCount (D:=D) d))
local notation3 (prettyPrint := false) "M" => (C).machine
local notation3 (prettyPrint := false) "G₁" => SewnTape.wiring p fit free pins
variable (hp : (fieldSewParams (SewnTape.wiring p fit free pins) (Fintype.card (Cube D)) d).Valid)
    (q : (packHistory (Subtype.mk (Boundary.seedState S (tapeTemplate p fit pins) d order position copies table words) good)
      plan.compiled.machine.epoch T).Index)
local notation3 (prettyPrint := false) "lastState" => ((packHistory (Pack := Admissible goodState) (K := fan S) leaf (M).epoch T).term q).val
local notation3 (prettyPrint := false) "net" => EnrichedTape.network (pins := pins) p fit position free count M leaf rfl q

open BorderVNP.Cube (TableEntry)
open BorderVNP.Cube.Physical Packing.CellAddresses Packing.BottomReports
open BorderVNP.Packing.RoutingOutputs.NativeDemands
open RoutingISA RoutingISA.Evaluator RoutingISA.Evaluator.SignedPrep
open DiagonalTallyAllocation DiagonalTallyCellReports ReportDirectory

variable {F : Type} [Field F] (cube : FixedCube F) (α ξ : ℝ)
    (calibrated : plan.SignedLabelRows count link (cube.pred+1) α ξ)
    (lit : (UniversalMachine.programPrefix p).length+(TeamContraction.cutWidth (k+1)+a) = literal α (k+1))
    (hd : 0 < BorderVNP.Cube.alphabet α (k+1)) {cells : ℕ}
    (number : (Cube D → Deck (depth S (d+1) T+1)) ≃ Fin cells)

variable (parameters : RoutingISA.SignedTaskArena.Parameters)
local notation3 (prettyPrint := false) "gap" => parameters.privateGap
local notation3 (prettyPrint := false) "deliveries" => freeDirectory R r ((UniversalMachine.programPrefix p).length+(TeamContraction.cutWidth (k+1)+a))
  link tiles seedBlock ((fan S)^T*tiles) desc
local notation3 (prettyPrint := false) "cell" => fun v : (net).Site => number (reduceMove (depth S (d+1) T) ((lastState).route.origin v))
local notation3 (prettyPrint := false) "edge" => FieldExport.mergedEdges (fieldSewParams G₁ axes d) hp (lastState).rows.edge
local notation3 (prettyPrint := false) "port" => (finProdFinEquiv.toEmbedding : FreeBlock R tiles ↪ Fin ((R+1)*tiles))
local notation3 (prettyPrint := false) "original" => originalDescriptionRows M leaf q deliveries rfl order
local notation3 (prettyPrint := false) "live" => (Equiv.refl (FreeBlock R tiles)).toEmbedding
local notation3 (prettyPrint := false) "B" => signedCoreDirectory plan p fit W position code sites edges ports table words
  good seeds free count pos num hp q cube α ξ calibrated lit hd number gap

variable (arenaBase profileBits : ℕ)
local notation3 (prettyPrint := false) "arena" =>
  (CubeArena.selectedSizes arenaBase (BorderVNP.Cube.alphabet α (k+1)) ((R+1)*exterior ξ r (k+1))
    cells ((boundary S (d+1) T).edges+4*((R+1)*CoverScale.sites (Cube D) (d+1))) (deliveries).candidates
    (R+1) r (k+1) profileBits).selected cube.pred cube.b cube.h cube.copies cube.width
local notation3 (prettyPrint := false) "task" => (SignedTaskArena.Layout.mk arena (cube.cubeID e) parameters)
variable (frame origin : Fin (R+1) → ℕ)
local notation3 (prettyPrint := false) "charts" => fun u : Fin (R+1) =>
  reportLayout (task).before (task).after (frame u)
    (RoutingOutputs.controlsBase (origin u) (arena).cables cells (deliveries).entries ((R+1)*tiles))
    parameters.parameters parameters.siteWidth parameters.bodyCap (arena).stop

open VPVNP.BurstRAM RoutingISA.Transmission BorderVNP.Routing CellMacro.Generator
open FiniteEvaluator Cube.HostAddress Cube.Scatter Cube.NativeIntervals
open Packing.CellAddressCircuit Packing.CellAddressPhysical RoutingOutputs Packing.Directory
open Diagonal.ExternalSew.Fragments CompactMachine
open Cube.Tally Cube.Scatter.Assignment DiagonalTallyPacketEmit
open TeamContraction.JointHeader

local notation3 (prettyPrint := false) "privateRows" => NativeDemands.privatePair net cell edge port deliveries original live gap
local notation3 (prettyPrint := false) "liveRows" => NativeDemands.livePair net cell edge port deliveries original live gap
local notation3 (prettyPrint := false) "rosterOf" =>
  plan.signedReceivedRows p fit W position code sites edges ports table words good seeds free count pos num hp q cube α ξ
    calibrated lit hd number parameters arenaBase profileBits frame origin

local notation3 (prettyPrint := false) "sizes" => placedSize net (B).programs

set_option maxHeartbeats 8500000 in
/-- The selected team reads its own physical report. All other teams supply their
actual host copies without making a local report choice or fitting an argument. -/
theorem issuedSourceOneReport
    {x : Exterior R r link → Bool} {route : WireLayout (R+1) r link} {in₀ : Fin pins → Bool}
    {hist : Fin (R+1) → TeamHistory rw} {ib hb sb : Fin (R+1) → ℕ} {owner : ℕ → Fin (R+1)}
    {g : BorderVNP.Cube.SharedRows.Layout} {src : Fin (R+1) → ℕ → ℕ} {anchor : Fin (R+1)}
    {decl : LengthDeclaration cube.pred (BorderVNP.Cube.alphabet α (k+1))}
    {group : Fin (BorderVNP.Cube.alphabet α (k+1)) → Fin (R+1)}
    {template : DiagonalTallyPacketEmit.Frame} {id : TableEntry cube.pred cube.b cube.h cube.copies cube.width → ℕ}
    {recordCount : ℕ} (owned : BorderVNP.Cube.TeamRows.Returns (Fin (R+1)) arena rw)
    (uTeam : Fin (R+1))
    (cut : ReportsThrough (owned.pub uTeam) (owned.macros uTeam) (owned.finalRegs uTeam) (owned.output uTeam))
    {delivery : ReturnedDelivery G₁ in₀ x route deliveries privateRows liveRows owner (arena).cellBank (arena).cellStride
      hist (fun u => (G₁).pinLayout u (ib u) (hb u) (sb u))}
    (writer : SharedWriters delivery g src)
    (symbols : SymbolFrame g (src anchor) (arena).header.blocks cube.copies cube.h decl group)
    (handoff : OwnedHandoff delivery g src arena decl group template id recordCount owned)
    (matched : Matching arena (B).owners decl (delivery.receivedRows g group))
    (observed : ObservedOwned arena decl group owned (B).owners (delivery.receivedRows g group) matched.val)
    {levels ownerWidth fieldWord : ℕ} {σ : Type} [Fintype σ]
    (fields : Fields (B).siteRows (B).edgeRows (B).portRows cells levels ownerWidth fieldWord σ)
    (choice : Fin (R+1) → σ → Bool)
    (geometry : ∀ u, Packing.CellAddressPhysical.Represents net cell sizes (B).siteID edge port fields (choice u))
    (codes : ∀ c,(fields.cells c).val=c.val)
    (wordsFit : ∀ c, guessedSize net cell c+siteSize net cell c sizes+suppliedSize net cell c<2^fieldWord)
    (hk : ownerWidth≤fieldWord) (wordFit : fieldWord≤rw)
    (sourceFrame liveBase : ℕ) (before placed : Fin (R+1) → Memory rw)
    (image : ∀ u, Image fields ((B).siteID ∘ original) (port ∘ finProdFinEquiv.symm)
      (choice u) liveBase (readings (before u)))
    (slotted : ∀ u,(privateLayout ((hist u).pub 0).val liveBase (arena).cables cells (deliveries).entries
      (deliveries).description gap).Image (readings (before u)) (deliveries).entries (readings (placed u)))
    (fits : ∀ u,(privateLayout ((hist u).pub 0).val liveBase (arena).cables cells (deliveries).entries
      (deliveries).description gap).Fits rw (readings (before u)))
    (headerReads : ∀ u,Header ((hist u).pub 0).val liveBase (arena).cables cells (deliveries).entries
      (readings (before u)))
    (reserve : sourceFrame+7*(deliveries).candidates≤liveBase) (endGeo : liveBase+5*(arena).cables≤(arena).header.header)
    (geoFit : liveBase<2^rw) (teamsFit : R+1≤2^rw) (processors : r≤2^rw) (fieldsFit : (deliveries).fields≤2^rw)
    (literalFit : (deliveries).literal<2^rw) (cellsFit : cells≤2^rw) (strideFit : (arena).cellStride≤2^rw)
    (capacity : ∀ c,suppliedSize net cell c+gap+(∑ j,if cell (original j)=c then (deliveries).description else 0)≤(arena).cellStride)
    {I : Type} [Fintype I] {sc : I → Fin cells} {sid : I ↪ ℕ} {sw : I → ℕ}
    (bf : Fin (R+1) → BroadcastFrame) (processor : ∀ u,Pins.ProcessorFields ((G₁).pinLayout u (ib u) (hb u) (sb u)))
    {guess : Fin (R+1) → ℕ → Bool}
    (source : ∀ u,ProfileRouteInputs (processor u) (bf u) (hist u).pub (guess u)
      (ISA.publish (placed u) ((hist u).pub 0).val sourceFrame ((deliveries).directory privateRows liveRows)))
    (team : ∀ u,(bf u).team=u.val)
    (write : ∀ u,SlottedWriter arena deliveries privateRows liveRows ((G₁).pinLayout u (ib u) (hb u) (sb u))
      (hist u).pub (placed u) sourceFrame sc sid sw)
    {initialHeader : Fin (R+1) → Fin 81 → Word rw} {fresh gates outputs bits off ell ctl X : ℕ}
    {dataBits : Fin (R+1) → List Bool} {claims : Fin (R+1) → List (List Bool)} {padding : Fin (R+1) → ℕ}
    {raw : Broadcast cube.pred (BorderVNP.Cube.alphabet α (k+1)) (arena).header.cap}
    (rawInput : ∀ u,PinnedRawInput (ar:=arena) (D:=deliveries) (pp:=privateRows) (lp:=liveRows)
      (pub:=(hist u).pub) (slotted:=placed u) (base:=sourceFrame) (bf u) (initialHeader u) fresh gates outputs
      bits off ell ctl (dataBits u) (claims u) (padding u) raw R X)
    (decoded : (Fin.ofNat (cube.pred+1) (readCode (cube.pred+1) raw.1),
      fun pair j => readCode ((arena).header.cap+1) (raw.2 pair j))=decl)
    {writerReg : Fin (R+1) → Bank rw}
    (issued : ∀ u, HeaderWriterReceipt arena deliveries privateRows liveRows owner decl group
      ((G₁).pinLayout u (ib u) (hb u) (sb u)) (bf u) (hist u).pub (hist u).macros (writerReg u)
      (ISA.publish (placed u) ((hist u).pub 0).val sourceFrame ((deliveries).directory privateRows liveRows)))
    (sharedRead : ∀ u,src u=readings (issued u).history.sharedInput)
    (input : Fin pins → Bool)
    (subst : ∀ u,Pins.SubstitutionAt ((G₁).pinLayout u (ib u) (hb u) (sb u)) (Pins.extendGuess input) (hist u).initial)
    (sections : Fin (R+1) → OpenSuffix.Inputs)
    {post : AfterTasks} {pre : Fin (R+1) → BeforeTasks}
    {banks : CellBanks.Layout} {cursor : ReportCursor} {description : ℕ}
    (ready : ∀ u, OpenSuffix.Ready (sections u) (owned.pub u 0).val (readings (owned.output u)) rw)
    (opened : ∀ u, OpenSuffix.Placement (sections u) (task).cube (pre u) (owned.pub u 0).val (readings (owned.output u)))
    (alloc : ReportAllocation (pre uTeam) post banks (charts uTeam) (((rosterOf) matched.val).cells uTeam) cursor)
    (seed : PreparedReportInput (owned.pub uTeam) cut.controls.val.2.2 (((rosterOf) matched.val).cells uTeam)
      cursor description)
    (bankStart : banks.bankStart=(arena).cellBank) (stride : banks.stride=(arena).cellStride) :
    let freeRoom := issuedReportFreeRoom (D:=D) (pins:=pins) (d:=d) p fit free
    ∃ memories : Fin (R+1) → Memory rw, memories uTeam=cut.reports.val.2.2 ∧
      (∀ t, t≠uTeam → readings (memories t)=OpenSuffix.hostImage (owned.pub t 0).val (readings (owned.output t))) ∧
      SourceWords net (B).cell (B).edgeID (B).portID hp.block freeRoom liveRows (arena).cellBank (arena).cellStride
        (freeBits G₁ input) (routedEnds net (B).cell (B).owners (B).slot matched.val)
        (fun c => readings (memories (((rosterOf) matched.val).order.symm c).1)) := by
  intro freeRoom
  have imageSource := plan.issuedHostSource p fit W position code sites edges ports table words good seeds free count
    pos num hp q cube α ξ calibrated lit hd number parameters arenaBase profileBits frame origin owned writer
    symbols handoff matched observed fields choice geometry codes wordsFit hk wordFit sourceFrame liveBase before
    placed image slotted fits headerReads reserve endGeo geoFit teamsFit processors fieldsFit literalFit cellsFit
    strideFit capacity bf processor source team write rawInput decoded issued sharedRead input subst sections opened
  have widths := plan.signedReceivedRows_widths p fit W position code sites edges ports table words good seeds free count
    pos num hp q cube α ξ calibrated lit hd number parameters arenaBase profileBits frame origin matched.val
  exact ((rosterOf) matched.val).sourceWords_one_report net (B).cell (B).edgeID (B).portID hp.block freeRoom liveRows
    (arena).cellBank (arena).cellStride (freeBits G₁ input) (routedEnds net (B).cell (B).owners (B).slot matched.val)
    arena sections uTeam cut (live_pair_slots net (B).cell (B).edgeID (B).portID original gap) ready
    (opened uTeam) alloc seed bankStart stride (fun i => (widths uTeam i).1.trans ((Packing.FinalReports.bank_sizes
      net (B).cell (fun v => ((B).programs v).program) (((rosterOf) matched.val).order ⟨uTeam,i⟩)).2.2)) imageSource

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI

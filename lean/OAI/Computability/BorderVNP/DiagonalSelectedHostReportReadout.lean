import OAI.Computability.BorderVNP.DiagonalReportSourcePlacement
import OAI.Computability.BorderVNP.DiagonalOneReportSourceWords
import OAI.Computability.BorderVNP.DiagonalSelectedIssuedOwnerTables
import OAI.Computability.BorderVNP.DiagonalSelectedIssuedSaved
import OAI.Computability.BorderVNP.DiagonalCanonicalFragmentPlacements
import OAI.Computability.BorderVNP.DiagonalSelectedReportSourceSlots
import OAI.Computability.BorderVNP.DiagonalSignedWriterReceipt
import OAI.Computability.BorderVNP.PackedFinalReportTemplate

/-! # Read one selected report from an authenticated original host image -/

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

local notation3 (prettyPrint := false) "packed" => plan.signedPackets count G₀ order position W code sites edges ports table
  words good cube α ξ calibrated lit hd hp number gap q

/-- A global cell is read on the same original selector that names its
team in the candidate's packet directory. -/
theorem reportHostTeam (v : Routed (b:=cube.b) (s:=cube.width) (B).owners) (c : Fin cells) :
    (((rosterOf) v).order.symm c).1=
      (B).owners v.1 ((packed).label c (BorderVNP.Cube.Physical.chosen cube.b cube.width v.1)) := by
  obtain ⟨⟨u,j⟩,rfl⟩ := ((rosterOf) v).order.surjective c
  rw [Equiv.symm_apply_apply]
  exact (plan.issuedReportRosterOwner p fit W position code sites edges ports table words good seeds free count
    pos num hp q cube α ξ calibrated lit hd number parameters arenaBase profileBits frame origin v u j).symm

local notation3 (prettyPrint := false) "reader(" v ")" =>
  fun c : Fin cells => (B).owners v.1 ((packed).label c (BorderVNP.Cube.Physical.chosen cube.b cube.width v.1))

set_option maxHeartbeats 8500000 in
/-- On the selected W chart the reported team can be changed independently
while retaining an already verified physical joint host source and the same routed selector. -/
theorem liftHostSourceOneReport (v : Routed (b:=cube.b) (s:=cube.width) (B).owners) (input : Fin pins → Bool)
    (owned : BorderVNP.Cube.TeamRows.Returns (Fin (R+1)) arena rw) (u : Fin (R+1))
    (cut : ReportsThrough (owned.pub u) (owned.macros u) (owned.finalRegs u) (owned.output u))
    (sections : Fin (R+1) → OpenSuffix.Inputs) {before : BeforeTasks} {after : AfterTasks} {banks : CellBanks.Layout}
    {cursor : ReportCursor} {description : ℕ}
    (ready : ∀ t, OpenSuffix.Ready (sections t) (owned.pub t 0).val (readings (owned.output t)) rw)
    (opened : OpenSuffix.Placement (sections u) (task).cube before (owned.pub u 0).val (readings (owned.output u)))
    (alloc : ReportAllocation before after banks (charts u) (((rosterOf) v).cells u) cursor)
    (seed : PreparedReportInput (owned.pub u) cut.controls.val.2.2 (((rosterOf) v).cells u) cursor description)
    (start : banks.bankStart=(arena).cellBank) (distance : banks.stride=(arena).cellStride)
    (host : SourceWords net (B).cell (B).edgeID (B).portID hp.block
      (issuedReportFreeRoom (D:=D) (pins:=pins) (d:=d) p fit free) liveRows (arena).cellBank (arena).cellStride
      (freeBits G₁ input) (routedEnds net (B).cell (B).owners (B).slot v)
      (fun c => OpenSuffix.hostImage (owned.pub (reader(v) c) 0).val (readings (owned.output (reader(v) c))))) :
    ∃ memories : Fin (R+1) → Memory rw, memories u=cut.reports.val.2.2 ∧
      (∀ t, t≠u → readings (memories t)=OpenSuffix.hostImage (owned.pub t 0).val (readings (owned.output t))) ∧
      SourceWords net (B).cell (B).edgeID (B).portID hp.block
        (issuedReportFreeRoom (D:=D) (pins:=pins) (d:=d) p fit free) liveRows (arena).cellBank (arena).cellStride
        (freeBits G₁ input) (routedEnds net (B).cell (B).owners (B).slot v)
        (fun c => readings (memories (reader(v) c))) := by
  have widths := plan.signedReceivedRows_widths p fit W position code sites edges ports table words good seeds free count
    pos num hp q cube α ξ calibrated lit hd number parameters arenaBase profileBits frame origin v
  have indices := plan.reportHostTeam p fit W position code sites edges ports table words good seeds free count
    pos num hp q cube α ξ calibrated lit hd number parameters arenaBase profileBits frame origin v
  let home := fun t => OpenSuffix.hostImage (owned.pub t 0).val (readings (owned.output t))
  have source := host.reindexOwners home (fun c => (indices c).symm)
  obtain ⟨memories,atTeam,other,readback⟩ := ((rosterOf) v).sourceWords_one_report net (B).cell (B).edgeID (B).portID hp.block
    (issuedReportFreeRoom (D:=D) (pins:=pins) (d:=d) p fit free) liveRows (arena).cellBank (arena).cellStride
    (freeBits G₁ input) (routedEnds net (B).cell (B).owners (B).slot v) arena sections u cut
    (live_pair_slots net (B).cell (B).edgeID (B).portID original gap) ready opened alloc seed start distance
    (fun i => (widths u i).1.trans ((Packing.FinalReports.bank_sizes net (B).cell (fun t => ((B).programs t).program)
      (((rosterOf) v).order ⟨u,i⟩)).2.2)) source
  exact ⟨memories,atTeam,other,readback.reindexOwners (fun t => readings (memories t)) indices⟩

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI

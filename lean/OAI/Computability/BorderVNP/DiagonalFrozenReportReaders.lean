import OAI.Computability.BorderVNP.CubePhysicalReceivedReportReaders
import OAI.Computability.BorderVNP.DiagonalCanonicalIndividualReturns
import OAI.Computability.BorderVNP.DiagonalRetainedBankExtension
import OAI.Computability.BorderVNP.DiagonalReceivedCanonicalGuard
import OAI.Computability.BorderVNP.DiagonalReceivedReportGuard
import OAI.Computability.BorderVNP.DiagonalRecoveredTermReaders
import OAI.Computability.BorderVNP.DiagonalSelectedReportRows
import OAI.Computability.BorderVNP.DiagonalCompiledGuardedHistory
import OAI.Computability.BorderVNP.DiagonalFrozenNumberedSeedObserved
import OAI.Computability.BorderVNP.DiagonalFrozenSeedReportSource
import OAI.Computability.BorderVNP.DiagonalWiredReturnedReportRows
import OAI.Computability.BorderVNP.DiagonalCheckedSeedReportRows

/-! # The signed report readers of the selected geometric history -/

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

variable {D m : ℕ} [NeZero D] {K E Gadget : Type} [Field K] [Field E] {e : PaidIdentity K D m} {S : SiteSchedule e}
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
    (parameters : RoutingISA.SignedTaskArena.Parameters)
    (param : PairedParameters k s ≃ Fin parameters.parameters)
    (scalar : Gadget ≃ Fin parameters.report.gadgets)
    {ns ne np : ℕ}
    (sites : (W.routedFine position).Site ↪ Fin ns) (edges : (W.routedFine position).Edge ↪ Fin ne)
    (ports : Fin r × Fin (publicWidth (tapeTemplate p fit pins)) ↪ Fin np)
    (table : (seedBundle (tapeTemplate p fit pins) (Fintype.card (Cube D)) d order position copies).Tables K)
local notation3 (prettyPrint := false) "code" => param.toEmbedding.trans Fin.valEmbedding
local notation3 (prettyPrint := false) "num" => scalar.toEmbedding.trans Fin.valEmbedding
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
    (y : e.Entry → E) (hy : ∀ f : MvPolynomial e.Entry ℤ, MvPolynomial.eval₂Hom (Int.castRingHom K) e.entry f = 0 →
      MvPolynomial.eval₂Hom (Int.castRingHom E) y f = 0)
    (pos : e.Entry → Gadget)
local notation3 (prettyPrint := false) "goodState" => Boundary.Good (S := S) (start := d+1) (P := Fin tiles)
  (bits := fun _ => copies*GridHosts.inputBlockWidth r (k+1) axes d)
  (shape := boundary S (d+1)) (w := word₀) budget
local notation3 (prettyPrint := false) "leaf" => (Subtype.mk (Boundary.seedState S G₀ d order position copies table words) good : Admissible goodState 0)
local notation3 (prettyPrint := false) "M" => (C).machine
local notation3 (prettyPrint := false) "G₁" => SewnTape.wiring p fit free pins
variable (hp : (fieldSewParams (SewnTape.wiring p fit free pins) (Fintype.card (Cube D)) d).Valid)
    (q : (packHistory (Subtype.mk (Boundary.seedState S (tapeTemplate p fit pins) d order position copies table words) good)
      plan.compiled.machine.epoch T).Index)
local notation3 (prettyPrint := false) "lastState" => ((packHistory (Pack := Admissible goodState) (K := fan S) leaf (M).epoch T).term q).val
local notation3 (prettyPrint := false) "net" => EnrichedTape.network (pins := pins) p fit position free count M leaf rfl q
local notation3 (prettyPrint := false) "host" => ((Equiv.sigmaEquivProd (Fin ((fan S)^T)) (Fin axes → Deck (d+2))).symm.toEmbedding.trans
  (enrichedOuterHosts M leaf q).site)
local notation3 (prettyPrint := false) "slabs" => fun j : Fin ((fan S)^T) × (Fin axes → Deck (d+2)) => W.seedSlab position code sites edges ports j.2
local notation3 (prettyPrint := false) "hidden" => W.bottomChoicesEquiv position edges slabs (fun _ => rfl)

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

local notation3 (prettyPrint := false) "gap" => parameters.privateGap
local notation3 (prettyPrint := false) "deliveries" => freeDirectory R r ((UniversalMachine.programPrefix p).length+(TeamContraction.cutWidth (k+1)+a))
  link tiles seedBlock ((fan S)^T*tiles) desc
local notation3 (prettyPrint := false) "cell" => fun v : (net).Site => number (reduceMove (depth S (d+1) T) ((lastState).route.origin v))
local notation3 (prettyPrint := false) "edge" => FieldExport.mergedEdges (fieldSewParams G₁ axes d) hp (lastState).rows.edge
local notation3 (prettyPrint := false) "port" => (finProdFinEquiv.toEmbedding : FreeBlock R tiles ↪ Fin ((R+1)*tiles))
local notation3 (prettyPrint := false) "original" => originalDescriptionRows M leaf q deliveries rfl order
local notation3 (prettyPrint := false) "live" => (Equiv.refl (FreeBlock R tiles)).toEmbedding
local notation3 (prettyPrint := false) "packed" => plan.signedPackets count G₀ order position W code sites edges ports table
  words good cube α ξ calibrated lit hd hp number gap q

local notation3 (prettyPrint := false) "B" => signedCoreDirectory plan p fit W position code sites edges ports table words
  good seeds free count pos num hp q cube α ξ calibrated lit hd number gap

variable (arenaBase profileBits : ℕ)
local notation3 (prettyPrint := false) "arena" =>
  (CubeArena.selectedSizes arenaBase (BorderVNP.Cube.alphabet α (k+1)) ((R+1)*exterior ξ r (k+1))
    cells ((boundary S (d+1) T).edges+4*((R+1)*CoverScale.sites (Cube D) (d+1))) (deliveries).candidates
    (R+1) r (k+1) profileBits).selected cube.pred cube.b cube.h cube.copies cube.width
local notation3 (prettyPrint := false) "task" => (SignedTaskArena.Layout.mk arena (cube.cubeID e) parameters)
variable (frame origin : ℕ)
local notation3 (prettyPrint := false) "chart" =>
  reportLayout (task).before (task).after frame
    (RoutingOutputs.controlsBase origin (arena).cables cells (deliveries).entries ((R+1)*tiles))
    parameters.parameters parameters.siteWidth parameters.bodyCap (arena).stop
local notation3 (prettyPrint := false) "home" => fun j : Fin (deliveries).entries => (B).cell (original j)
local notation3 (prettyPrint := false) "charges" => placedSize net (B).programs
local notation3 (prettyPrint := false) "sourceSlot" => fun j : Fin (deliveries).entries =>
  (arena).cellBank+(home j).val*(arena).cellStride+
    (RoutingOutputs.NativeDemands.destination net cell edge port deliveries original live gap (.inl j)).2
local notation3 (prettyPrint := false) "boxStart" => fun j : Fin (deliveries).entries =>
  siteBase net (B).cell (home j) (B).siteID charges (Subtype.mk (original j) rfl)
local notation3 (prettyPrint := false) "bundleIdx" =>
  (descriptionOrder (leaf).val.pack ((fan S)^T) tiles (deliveries).entries rfl order).trans
    (Equiv.sigmaEquivProd (Fin ((fan S)^T)) (Fin axes → Deck (d+2)))
local notation3 (prettyPrint := false) "ch" => (groupedGridRows G₀ axes d order position copies).edge
local notation3 (prettyPrint := false) "gp" => (Equiv.refl (Fin tiles)).toEmbedding


open BorderVNP.Cube.Physical.NativeLedger EnrichedTape
attribute [local instance] WiredWitness.reportDeckEq

/-- The nested row-major team indices of this same signed execution. -/
noncomputable local instance frozenLedgerTeams {q₀ m₀ t₀ : ℕ} : Fintype (Port q₀ (Fin m₀ × Unit) t₀) :=
  Replay.batchFinite q₀ (Fin m₀ × Unit) t₀

local notation3 (prettyPrint := false) "coreRows" => fun c : Fin (B).cells =>
  (BundleDirectory.sourceRows home c.val).map (fun j => W.seedCoreBundle position code sites edges ports
    (bundleIdx j).2 (sourceSlot j) (boxStart j) copies)
local notation3 (prettyPrint := false) "rr(" v ")" => plan.signedReceivedRows p fit W position code sites edges ports table words
  good seeds free count pos num hp q cube α ξ calibrated lit hd number parameters arenaBase profileBits (fun _ => frame)
  (fun _ => origin) (v).val
variable (pin : Ports (fun _ : FreeBlock R (GridHosts.tileCount (Fintype.card (Cube D)) d) =>
    GridHosts.inputBlockWidth r (k+1) (Fintype.card (Cube D)) d))
    (tape : Fin (R+1) → ℕ → Bool) (start : Fin (R+1) → ℕ) (cursor : Fin (R+1) → ReportCursor)
local notation3 (prettyPrint := false) "sourceCell(" v "," raw "," j ")" => (rr(v)).assignedAt net (B).cell (B).siteID
  (B).edgeID (B).portID (B).programs (B).owners (B).slot pin (B).owner coreRows (v).val raw (j).1 (j).2
local notation3 (prettyPrint := false) "atReport(" v "," v0 ")" => (rr(v)).reportedWithTape tape start v0
local notation3 (prettyPrint := false) "stages(" v "," raw "," c ")" => CellAddresses.bank net (B).cell c charges
  (privateWires net (B).cell charges c ((raw) c)) (privateStaging net (B).cell charges c ((raw) c))
  (pathSupply net (B).cell (B).edgeID (B).portID (B).owners (B).slot pin (v).val c)
local notation3 (prettyPrint := false) "currentPath(" v "," raw ")" => rawPath net (B).cell (B).edgeID (B).programs (B).owners (v).val raw
local notation3 (prettyPrint := false) "stageWidth" => plan.signedCore_widths p fit W position code sites edges ports
  table words good seeds free count pos num hp q cube α ξ calibrated lit hd number gap
local notation3 (prettyPrint := false) "assignment(" v "," raw ")" => extractBottom net (B).cell (B).siteID charges (B).owners
  slabs (fun _ => copies) (fun _ j => retainedLocation net (B).programs host slabs (fun _ => copies) stageWidth j) (v).val raw
local notation3 (prettyPrint := false) "traced(" v "," raw ")" =>
  EnrichedTape.tags p fit W position free count M leaf rfl y hy pos hp.block q (hidden (assignment(v,raw)))
local notation3 (prettyPrint := false) "numTags(" v "," raw ")" => numberTables param scalar (traced(v,raw)).tags
local notation3 (prettyPrint := false) "numWords(" v "," raw ")" => (traced(v,raw)).words.number
  (SewnTape.teamNumber (fan S) T copies R count) param scalar
local notation3 (prettyPrint := false) "members(" v ")" => (t : Fin (R+1)) × Fin ((rr(v)).cells t).length

/-- Every published report cell was visited by the actual owner on this returned path. -/
theorem signedReportVisitOwner (v : (B).Route cube.width) (raw : (B).Bank) (j : members(v)) :
    pathCellOwner (packed).label ((B).owners v.val.1) (currentPath(v,raw)) ((rr(v)).order j)=j.1 :=
  plan.signedReceivedRows_owner p fit W position code sites edges ports table words good seeds free count pos num hp q
    cube α ξ calibrated lit hd number parameters arenaBase profileBits (fun _ => frame) (fun _ => origin) v.val j.1 j.2

local notation3 (prettyPrint := false) "visitOwner(" v "," raw ")" => plan.signedReportVisitOwner p fit W position
  parameters param scalar sites edges ports table words good seeds free count pos hp q cube α ξ calibrated lit hd number
  arenaBase profileBits frame origin v raw
/-- The complete operand readers on the actual frozen packet, at its real returned team and cell order. -/
noncomputable abbrev signedReportReaderAt (v : (B).Route cube.width) (raw : (B).Bank) (t : Fin (R+1)) :=
  (rr(v)).pathReportReaders (N := net) («cell» := (B).cell) (l := chart) («B» := Nat.clog 2 (r*(2*k+1)+1))
    (B).slot (numTags(v,raw)) pin (numWords(v,raw)) (packed).label ((B).owners v.val.1) (currentPath(v,raw))
    (visitOwner(v,raw)) tape start t

local notation3 (prettyPrint := false) "growth" => plan.signedCore_wellFormed p fit W position code sites edges ports
  table words good seeds free count pos num hp q cube α ξ calibrated lit hd number gap
local notation3 (prettyPrint := false) "tagAgreement" => plan.signedCore_model p fit W position code sites edges ports
  table words good seeds free count y hy pos num hp q cube α ξ calibrated lit hd number gap
local notation3 (prettyPrint := false) "recordsAt(" v "," raw ")" => fun j : Fin (deliveries).entries =>
  CellSparse.lookup (stages(v,raw,home j) ++ (atReport(v,home j)).bits)

local notation3 (prettyPrint := false) "assignedSources(" v "," raw ")" => fun j : members(v) => sourceCell(v,raw,j)
local notation3 (prettyPrint := false) "frozenBase(" v "," raw ")" => (rr(v)).reportSourceBank
  (assignedSources(v,raw)) home
local notation3 (prettyPrint := false) "retained(" banks ")" => W.retainedBundle (copies:=copies) position bundleIdx
  code sites edges ports ch gp sourceSlot boxStart banks

/-- Appending the reported tally preserves the chosen parameter digit from each original work slab. -/
private theorem signedLedgerBank (v : (B).Route cube.width) (raw : (B).Bank) (j : Fin (deliveries).entries) :
    retained(recordsAt(v,raw)) j = retained(frozenBase(v,raw)) j := by
  let dir := B
  let rc := rr(v)
  let src := fun j : members(v) => sourceCell(v,raw,j)
  let cores := coreRows
  let out := rc.reportedWithTape tape start
  let pre := fun c : Fin dir.cells => stages(v,raw,c)
  let primal := fun j : Fin (deliveries).entries => CellSparse.lookup (pre (home j))
  let actual := recordsAt(v,raw)
  have bankEq : rc.reportSourceBank src home = primal :=
    funext (rc.sourceBank_assignedAt net dir.cell dir.siteID dir.edgeID dir.portID dir.programs dir.owners dir.slot
      pin dir.owner cores v.val raw home)
  change retained(actual) j = retained(rc.reportSourceBank src home) j
  rw [bankEq]
  exact W.retainedBundle_host_bank_append position bundleIdx code sites edges ports ch gp sourceSlot boxStart
      net dir.cell dir.siteID dir.programs host stageWidth (fun c => privateWires net dir.cell charges c (raw c))
      (fun c => privateStaging net dir.cell charges c (raw c))
      (pathSupply net dir.cell dir.edgeID dir.portID dir.owners dir.slot pin v.val) (fun _ => rfl)
      (fun c => (out c).bits) j

/-- The physical size fields span the private word and supplied boundary of exactly this staged cell. -/
private theorem signedLedgerExtent (v : (B).Route cube.width) (raw : (B).Bank) (j : members(v)) :
    (((rr(v)).cells j.1).get j.2).privateWires+(((rr(v)).cells j.1).get j.2).supplied =
      (sourceCell(v,raw,j)).privateWires+(sourceCell(v,raw,j)).boundary.length :=
  (B).received_extent (rr(v)) pin coreRows (v,raw) j.1 j.2
    (plan.signedReceivedRows_widths p fit W position code sites edges ports table words good seeds free
      count pos num hp q cube α ξ calibrated lit hd number parameters arenaBase profileBits (fun _ => frame)
      (fun _ => origin) v.val j.1 j.2)

local notation3 (prettyPrint := false) "lengthsAt(" v "," raw ")" => signedLedgerExtent plan p fit W position
  parameters param scalar sites edges ports table words good seeds free count pos hp q cube α ξ calibrated lit hd number
  arenaBase profileBits frame origin pin v raw
local notation3 (prettyPrint := false) "sameAt(" v "," raw ")" => signedLedgerBank plan p fit W position
  parameters param scalar sites edges ports table words good seeds free count pos hp q cube α ξ calibrated lit hd number
  arenaBase profileBits frame origin pin tape start v raw

/-- Reconstruct each original birth receipt on its actual augmented bank, then carry the observed digits
through the compiled path to the numbered power occurrences. -/
private theorem signedObservedPowers {w₀ order₀ : ℕ} (v : (B).Route cube.width) (raw : (B).Bank)
    (pass : ∀ j : members(v), (sourceCell(v,raw,j)).Passing w₀ order₀)
    (ret : ∀ j : members(v), ∃ time, (sourceCell(v,raw,j)).Returns w₀ order₀ (atReport(v,(rr(v)).order j)) time)
    : EnrichedTape.SeedReportObserved (l:=chart) p fit W position free count M leaf rfl y hy pos hp.block q
      (hidden (assignment(v,raw))) (B).slot (currentPath(v,raw)) pin bundleIdx param sites edges ports ch gp
      sourceSlot boxStart (recordsAt(v,raw)) := by
  let dir := B
  let rc := rr(v)
  let src := fun j : members(v) => sourceCell(v,raw,j)
  let cores := coreRows
  let out := rc.reportedWithTape tape start
  let pre := fun c : Fin dir.cells => stages(v,raw,c)
  let primal := fun j : Fin (deliveries).entries => CellSparse.lookup (pre (home j))
  let actual := recordsAt(v,raw)
  let stored := plan.signedReceivedRows_bundles p fit W position code sites edges ports table words good seeds free
    count pos num hp q cube α ξ calibrated lit hd number parameters arenaBase profileBits (fun _ => frame) (fun _ => origin) v.val
  have bankEq : rc.reportSourceBank src home = primal :=
    funext (rc.sourceBank_assignedAt net dir.cell dir.siteID dir.edgeID dir.portID dir.programs dir.owners dir.slot
      pin dir.owner cores v.val raw home)
  have grouped := W.returned_seed_rows position bundleIdx code sites edges ports ch gp sourceSlot boxStart rc tape start
    src (fun _ => rfl) pass ret home (fun _ _ => false) (fun _ => rfl) (fun j => stored j.1 j.2)
  rw [bankEq] at grouped
  let baseDir := fun c : Fin dir.cells => FinalCell.directory dir.owner net (fun x => (dir.cell x).val)
    dir.siteID dir.edgeID dir.portID (fun x => (dir.programs x).program) c.val (rc.countReports net dir.cell dir.programs c)
  have checked (c : Fin dir.cells) := rc.returnedCertificate_assignedAt net dir.cell dir.siteID dir.edgeID dir.portID
    dir.programs dir.owners dir.slot pin dir.owner cores v.val raw tape start pass ret c
  have originalCore := dir.corePassed_of_received rc pin cores (v,raw) host slabs (fun _ => copies) stageWidth num
    (fun z => (EnrichedTape.tags p fit W position free count M leaf rfl y hy pos hp.block q (hidden z)).tags)
    tagAgreement (fun x => (growth x).1) (fun x => (growth x).2.1) (fun x => (growth x).2.2.1) pass
  have observations := frozenSigned_reportSource p fit W position code sites edges ports table C words good seeds
    free count y hy pos num hp q dir.cell dir.siteID dir.owners dir.slot pin v.val raw bundleIdx sourceSlot boxStart out
    baseDir originalCore grouped (dir.returnedBank_extent rc pin cores (v,raw) tape start (lengthsAt(v,raw)))
    (fun _ => rfl) (fun c => ⟨_,checked c⟩)
  exact (C).frozenNumberedSeedObserved (l:=chart) p fit W position sites edges ports table
    words good seeds (num ∘ pos) free count y hy pos hp q (hidden (assignment(v,raw))) dir.slot (currentPath(v,raw))
    pin param bundleIdx sourceSlot boxStart actual observations

include cursor in
/-- The augmented private checker, the ordered report writer, and the
selected owner's tally supply these readers on one and the same native path. -/
noncomputable def signedReportReaders {w₀ order₀ : ℕ} (v : (B).Route cube.width) (raw : (B).Bank)
    (pass : ∀ j : members(v), (sourceCell(v,raw,j)).Passing w₀ order₀)
    (ret : ∀ j : members(v), ∃ time, (sourceCell(v,raw,j)).Returns w₀ order₀ (atReport(v,(rr(v)).order j)) time)
    (t : Fin (R+1)) :
    plan.signedReportReaderAt p fit W position parameters param scalar sites edges ports table words good seeds
      free count y hy pos hp q cube α ξ calibrated lit hd number arenaBase profileBits frame origin pin tape start v raw t := by
  let rc := rr(v)
  exact EnrichedTape.recoveredTermReaders (l:=chart) p fit W position free count M leaf rfl y hy pos hp.block q
    B (packed).label v raw pin rc param scalar bundleIdx sites edges ports ch gp sourceSlot boxStart
    (fun _ _ => false) host stageWidth (fun x => (growth x).1) (fun x => (growth x).2.1)
    (fun x => (growth x).2.2.1) tape start cursor tagAgreement pass ret (lengthsAt(v,raw))
    (fun j => plan.signedReceivedRows_bundles p fit W position code sites edges ports table words good seeds free
      count pos num hp q cube α ξ calibrated lit hd number parameters arenaBase profileBits
      (fun _ => frame) (fun _ => origin) v.val j.1 j.2) (visitOwner(v,raw)) (recordsAt(v,raw)) (sameAt(v,raw))
    (signedObservedPowers plan p fit W position parameters param scalar sites edges ports table words good seeds
      free count y hy pos hp q cube α ξ calibrated lit hd number arenaBase profileBits frame origin pin tape start
      v raw pass ret) t

local notation3 (prettyPrint := false) "batchCells(" v "," raw ")" =>
  (rr(v)).assigned net (B).cell (B).siteID (B).edgeID (B).portID (B).programs (B).owners (B).slot pin (B).owner
    coreRows (v).val raw
local notation3 (prettyPrint := false) "returnedProposal(" v "," raw "," pass ")" =>
  ((rr(v)).physicalReportEquiv net (B).cell (B).siteID (B).edgeID (B).portID (B).programs (B).owners (B).slot pin
    (B).owner coreRows (v).val raw (rr(v)).cells (fun _ => rfl)).symm
    (DiagonalTallyCellReports.canonicalReports (batchCells(v,raw)) pass)

include cursor in
/-- On the canonical inverse, the only hypothesis is that the decoded batch
passed. Its actual native report tape supplies each individual returning cell. -/
noncomputable def signedCanonicalReportReaders {w₀ order₀ : ℕ} (v : (B).Route cube.width) (raw : (B).Bank)
    (pass : ∀ u c, c ∈ batchCells(v,raw) u → c.Passing w₀ order₀) (t : Fin (R+1)) :
    plan.signedReportReaderAt p fit W position parameters param scalar sites edges ports table words good seeds
      free count y hy pos hp q cube α ξ calibrated lit hd number arenaBase profileBits frame origin pin
      ((rr(v)).sourceReportStream (returnedProposal(v,raw,pass))) (fun _ => 0) v raw t := by
  let rc := rr(v)
  have passes := rc.assignedAt_passing net (B).cell (B).siteID (B).edgeID (B).portID (B).programs (B).owners (B).slot
    pin (B).owner coreRows v.val raw pass
  have returns := rc.canonical_individual_returns net (B).cell (B).siteID (B).edgeID (B).portID (B).programs (B).owners
    (B).slot pin (B).owner coreRows v.val raw pass
  exact plan.signedReportReaders p fit W position parameters param scalar sites edges ports table words good seeds
    free count y hy pos hp q cube α ξ calibrated lit hd number arenaBase profileBits frame origin pin
    (rc.sourceReportStream (returnedProposal(v,raw,pass))) (fun _ => 0) cursor v raw passes returns t

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI

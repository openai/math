import OAI.Computability.BorderVNP.DiagonalCandidatePrefixFinish
import OAI.Computability.BorderVNP.DiagonalCanonicalSameRows
import OAI.Computability.BorderVNP.DiagonalFrozenReportReaders

/-! # The canonical positive finish on a selected original signed assignment -/

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


open BorderVNP.Cube.Physical.NativeLedger EnrichedTape
attribute [local instance] WiredWitness.reportDeckEq

attribute [local instance] frozenLedgerTeams

local notation3 (prettyPrint := false) "coreRows" => fun c : Fin (B).cells =>
  (BundleDirectory.sourceRows home c.val).map (fun j => W.seedCoreBundle position code sites edges ports
    (bundleIdx j).2 (sourceSlot j) (boxStart j) copies)
local notation3 (prettyPrint := false) "rr(" v ")" => plan.signedReceivedRows p fit W position code sites edges ports table words
  good seeds free count pos num hp q cube α ξ calibrated lit hd number parameters arenaBase profileBits (fun _ => frame)
  (fun _ => origin) (v).val
variable (pin : Ports (fun _ : FreeBlock R (GridHosts.tileCount (Fintype.card (Cube D)) d) =>
    GridHosts.inputBlockWidth r (k+1) (Fintype.card (Cube D)) d))
    (cursor : Fin (R+1) → ReportCursor)
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

local notation3 (prettyPrint := false) "visitOwner(" v "," raw ")" => plan.signedReportVisitOwner p fit W position
  parameters param scalar sites edges ports table words good seeds free count pos hp q cube α ξ calibrated lit hd number
  arenaBase profileBits frame origin v raw
local notation3 (prettyPrint := false) "batchCells(" v "," raw ")" =>
  (rr(v)).assigned net (B).cell (B).siteID (B).edgeID (B).portID (B).programs (B).owners (B).slot pin (B).owner
    coreRows (v).val raw

open RoutingISA.Evaluator TeamContraction.JointHeader CompactMachine CellMacro.Generator DiagonalTallyCellReports
open VPVNP.BurstRAM

local notation3 (prettyPrint := false) "ctl" =>
  RoutingOutputs.controlsBase origin (arena).cables cells (deliveries).entries ((R+1)*tiles)
local notation3 (prettyPrint := false) "chartAt" f =>
  DiagonalTallyAllocation.reportLayout (task).before (task).after f ctl parameters.parameters
    parameters.siteWidth parameters.bodyCap (arena).stop
local notation3 (prettyPrint := false) "srcEquiv(" v "," raw ")" =>
  (rr(v)).physicalReportEquiv net (B).cell (B).siteID (B).edgeID (B).portID (B).programs (B).owners
    (B).slot pin (B).owner coreRows (v).val raw (rr(v)).cells (fun _ => rfl)
local notation3 (prettyPrint := false) "counts(" v "," raw "," gid ")" =>
  physicalRow (B).slot (numTags(v,raw)) pin
    (fun (_ : BorderVNP.Cube.Packet (task).cube.n (task).cube.header.d (task).cube.header.blocks) => gid)
    (numWords(v,raw)) (packed).label ((B).owners (v).val.1) (currentPath(v,raw))

include cursor in
/-- The canonical reports of the checked selected source provide every
semantic operand at every proposed subtotal. The finite tapes in the prefix
runs are the actual inverse proposals in their physical owner order. -/
theorem signedReceived_returnedFinish
    {clockWidth inputNumber reserve₀ groups₀ cap₀ tallyWidth : ℕ} {gen : Fragment IO}
    (v : (B).Route cube.width) (raw : (B).Bank)
    (X : UncheckedCandidate (task).id gen inputNumber clockWidth (R+1) (task).dim tallyWidth)
    (hdr : PositiveFields reserve₀ (task).cube.n groups₀ cap₀ (R+1) (task).dim tallyWidth)
    (common : X.layout=fun _ => chart) (assigned : HEq X.assigned (batchCells(v,raw)))
    (startup : Fin (R+1) → TeamContraction.ProcessorSlots.StartupArena)
    (gid : TableEntry (task).cube.n (task).cube.b (task).cube.h (task).cube.K (task).cube.s →
      Fin parameters.report.gadgets)
    (pubFrame : ∀ (ok : ∀ u c,c∈X.assigned u → c.Passing clockWidth inputNumber)
      (cc : Fin ((R+1)*(task).dim*tallyWidth) → Bool) (t : Fin (R+1)),
      frame=((X.team (canonicalReports X.assigned ok) cc t).pub 0).val)
    (runs : ∀ (ok : ∀ u c,c∈X.assigned u → c.Passing clockWidth inputNumber) cc t,
      let reports := canonicalReports X.assigned ok
      let team := X.team reports cc t
      let pr := (X.candidate reports cc).1 t
      let layout := congrArg (fun f => chartAt f) (pubFrame ok cc t)
      let src := (srcEquiv(v,raw)).symm (reportsOfSameRows common assigned reports)
      let tapes := fun u => (reportAssignmentEquiv ((rr(v)).cells u)).symm (src u)
      PrefixFinishRun task team pr ctl parameters.siteWidth parameters.bodyCap gid ((B).owners v.val.1)
        (currentPath(v,raw)) ((rr(v)).atLayout layout) t ((rr(v)).tapesAtLayout layout tapes)
        (startup t) (hdr.withSubtotals cc))
    (numbered : Fin (R+1) → Fin (task).dim → ℕ) (sameCounts : counts(v,raw,gid)=numbered)
    (bound : ∀ t i,numbered t i<2^clockWidth) : X.ReturnedFinish hdr numbered (fun _ => task) startup := by
  refine returnedFinish_of_canonicalReaders task X hdr (B).slot (numTags(v,raw)) pin gid (numWords(v,raw))
    (packed).label ((B).owners v.val.1) (currentPath(v,raw)) ctl parameters.siteWidth parameters.bodyCap
    startup frame (rr(v)) (fun native => (srcEquiv(v,raw)).symm (reportsOfSameRows common assigned native))
    (visitOwner(v,raw)) pubFrame runs ?_ numbered sameCounts bound
  intro ok t
  have pass := passing_of_same_rows common.symm assigned.symm ok
  let readAt (r₀ : NativeReports (batchCells(v,raw))) :=
    (rr(v)).pathReportReaders (N := net) («cell» := (B).cell) («B» := Nat.clog 2 (r*(2*k+1)+1))
      (B).slot (numTags(v,raw)) pin (numWords(v,raw)) (packed).label ((B).owners v.val.1)
      (currentPath(v,raw)) (visitOwner(v,raw)) ((rr(v)).sourceReportStream ((srcEquiv(v,raw)).symm r₀))
      (fun _ => 0) t
  have read : readAt (canonicalReports (batchCells(v,raw)) pass) :=
    plan.signedCanonicalReportReaders p fit W position parameters param scalar sites edges ports table words
      good seeds free count y hy pos hp q cube α ξ calibrated lit hd number arenaBase profileBits frame origin
      pin cursor v raw pass t
  exact Eq.mpr (congrArg readAt (canonicalReports_sameRows common assigned ok)) read

/-- The typed raw runs on the one original received directory, with the
actual frame, proposal inverse, and full finite tape of each processor. -/
noncomputable abbrev signedReceivedPrefixRuns
    {clockWidth inputNumber reserve₀ groups₀ cap₀ tallyWidth : ℕ} {gen : Fragment IO}
    (v : (B).Route cube.width) (raw : (B).Bank)
    (X : UncheckedCandidate (task).id gen inputNumber clockWidth (R+1) (task).dim tallyWidth)
    (hdr : PositiveFields reserve₀ (task).cube.n groups₀ cap₀ (R+1) (task).dim tallyWidth)
    (common : X.layout=fun _ => chart) (assigned : HEq X.assigned (batchCells(v,raw)))
    (startup : Fin (R+1) → TeamContraction.ProcessorSlots.StartupArena)
    (gid : TableEntry (task).cube.n (task).cube.b (task).cube.h (task).cube.K (task).cube.s →
      Fin parameters.report.gadgets)
    (pubFrame : ∀ (ok : ∀ u c,c∈X.assigned u → c.Passing clockWidth inputNumber)
      (cc : Fin ((R+1)*(task).dim*tallyWidth) → Bool) (t : Fin (R+1)),
      frame=((X.team (canonicalReports X.assigned ok) cc t).pub 0).val) :=
  ∀ (ok : ∀ u c,c∈X.assigned u → c.Passing clockWidth inputNumber) cc t,
      let reports := canonicalReports X.assigned ok
      let team := X.team reports cc t
      let pr := (X.candidate reports cc).1 t
      let layout := congrArg (fun f => chartAt f) (pubFrame ok cc t)
      let src := (srcEquiv(v,raw)).symm (reportsOfSameRows common assigned reports)
      let tapes := fun u => (reportAssignmentEquiv ((rr(v)).cells u)).symm (src u)
      PrefixFinishRun task team pr ctl parameters.siteWidth parameters.bodyCap gid ((B).owners v.val.1)
        (currentPath(v,raw)) ((rr(v)).atLayout layout) t ((rr(v)).tapesAtLayout layout tapes)
        (startup t) (hdr.withSubtotals cc)

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI

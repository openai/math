import OAI.Computability.BorderVNP.DiagonalSelectedProtectedCompletion
import OAI.Computability.BorderVNP.DiagonalSelectedReturnedFinish
import OAI.Computability.BorderVNP.DiagonalSelectedReturnedCounts
import OAI.Computability.BorderVNP.RoutingISASignedPhysicalRoomParameters

/-! # Protected completion from the native cuts of the selected frozen run -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity
open Packing Packing.Inherited Packing.DeckGrid Packing.PhysicalEpochs Diagonal Diagonal.CellEntries
open Diagonal.ExternalSew TeamContraction ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar
open EnrichedOuter TeamScales BorderVNP.Cube.Physical.NativeAssignments BorderVNP.Cube
open Branch ResidueBox ResidueIndex ResiduePins
open scoped Classical BigOperators BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option Elab.async false
set_option maxHeartbeats 2400000
attribute [local irreducible] Nat.clog
set_option maxRecDepth 7000
set_option synthInstance.maxSize 4000

variable {D m : ℕ} [NeZero D] {K F : Type} [Field K] [Field F] {e : PaidIdentity K D m} {S : SiteSchedule e}
    {R r pin link k d a regs rw ec width s copies T header work : ℕ}
    (plan : SeedPlan S (k+1) r d T copies header work) (cube : FixedCube F) (φ : F →+* K)
    (ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))) {qchar : ℕ}
    {common : CommonField e (φ ∘ cube.table) qchar k s ord} (chart : AdvisedBranch common)
    (p : UniversalMachine.Program)
    (fit : 2*((UniversalMachine.programPrefix p).length+(TeamContraction.cutWidth (k+1)+a))+
      R*link+Wires.innerWidth r regs rw ec width ≤ k+1)
local notation3 (prettyPrint := false) "pins" => (pairedTableParameters (k+1) s+2)*pin
local notation3 (prettyPrint := false) "scalarIDs" => e.Entry ⊕ TableEntry cube.pred cube.b cube.h cube.copies cube.width
local notation3 (prettyPrint := false) "code" => (ParseTable.numberedLabelEquiv ord k s).toEmbedding.trans Fin.valEmbedding
local notation3 (prettyPrint := false) "num" => (Fintype.equivFin (scalarIDs)).toEmbedding.trans Fin.valEmbedding
local notation3 (prettyPrint := false) "axes" => Fintype.card (Cube D)
local notation3 (prettyPrint := false) "tiles" => GridHosts.tileCount axes d
local notation3 (prettyPrint := false) "G₀" => tapeTemplate p fit pins
variable {order : Fin (GridHosts.tileCount (Fintype.card (Cube D)) d) ≃ (Fin (Fintype.card (Cube D)) → Deck (d+2))}
    (W : WiredWitness (tapeTemplate p fit ((pairedTableParameters (k+1) s+2)*pin)) (Fin.last k) D (Fintype.card (Cube D)) d order
      (0 : ParseTable.State (Fin (k+1) × Bool) s))
    (position : (Fin (Fintype.card (Cube D)) → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    {ns ne np : ℕ}
    (sites : (W.routedFine position).Site ↪ Fin ns) (edges : (W.routedFine position).Edge ↪ Fin ne)
    (ports : Fin r × Fin (publicWidth (tapeTemplate p fit ((pairedTableParameters (k+1) s+2)*pin))) ↪ Fin np)
    (table : (seedBundle (tapeTemplate p fit ((pairedTableParameters (k+1) s+2)*pin)) (Fintype.card (Cube D)) d order position copies).Tables K)
local notation3 (prettyPrint := false) "M" => plan.compiled.machine
local notation3 (prettyPrint := false) "mass" => initialMass (D:=D) (k+1) r d copies header
local notation3 (prettyPrint := false) "goodState" => Boundary.Good (S := S) (start := d+1) (P := Fin tiles)
  (bits := fun _ => copies*GridHosts.inputBlockWidth r (k+1) axes d)
  (shape := boundary S (d+1)) (w := 60*logWidth r (k+1)) (boundaryBudget S mass)
variable (words : Boundary.Pins S (d+1) (boundary S (d+1)) (60*logWidth r (k+1)) 0 → Bool)
    (good : Boundary.Good (boundaryBudget S (initialMass (D:=D) (k+1) r d copies header)) 0 (Boundary.seedState S (tapeTemplate p fit ((pairedTableParameters (k+1) s+2)*pin)) d order position copies table words))
    (seeds : ∀ h, ∀ i : Fin S.rounds,
      ((Cube D → Deck (S.level (offset S (d+1) h) (i.val+1)+1)) × (S.source.pattern i).bins.Bin) → ℕ)
    (free : Fin (R+1) → Fin r → Fin a → Bool) (count : (fan S)^T*copies = R+1)
local notation3 (prettyPrint := false) "leaf" => (Subtype.mk (Boundary.seedState S G₀ d order position copies table words) good : Admissible goodState 0)
local notation3 (prettyPrint := false) "G₁" => SewnTape.wiring p fit free pins
local notation3 (prettyPrint := false) "Y" => chart.gadgets ∘ Sum.inl
local notation3 (prettyPrint := false) "Hist" => (packHistory (Pack := Admissible goodState) (K := fan S) leaf (M).epoch T).Index
variable (hp : (fieldSewParams (SewnTape.wiring p fit free ((pairedTableParameters (k+1) s+2)*pin)) (Fintype.card (Cube D)) d).Valid)
    (α ξ : ℝ) (calibrated : plan.SignedLabelRows count link (cube.pred+1) α ξ)
    (lit : (UniversalMachine.programPrefix p).length+(TeamContraction.cutWidth (k+1)+a) = literal α (k+1))
    (hd : 0 < BorderVNP.Cube.alphabet α (k+1)) {cells : ℕ}
    (number : (Cube D → Deck (depth S (d+1) T+1)) ≃ Fin cells)
    (reportArena : RoutingISA.CubeArena.Layout) (dirs : RoutingISA.SignedTaskArena.GeometryDirectories)
    (bundles marked expBits reportWord headerSize body : ℕ)
local notation3 (prettyPrint := false) "params" => RoutingISA.SignedTaskArena.physicalParameters reportArena dirs
  (k+1) bundles marked (pairedTableParameters (k+1) s) expBits (Fintype.card (scalarIDs)) reportWord headerSize body
local notation3 (prettyPrint := false) "gap" => (params).privateGap

attribute [local instance] selectedBatchFinite

local notation3 (prettyPrint := false) "banks" => canonicalBank (G := G₁) hp.block (GridHosts.gridRoom G₁ Fintype.card_pos)
local notation3 (prettyPrint := false) "tags" => EnrichedTape.tags (Gadget := scalarIDs) p fit W position free count M leaf rfl
  Y chart.preserves_paid Sum.inl hp.block
local notation3 (prettyPrint := false) "dir" => signedCoreDirectory plan p fit W position code sites edges ports table words
  good seeds free count Sum.inl num hp
local notation3 (prettyPrint := false) "put" => (Sum.inr : TableEntry cube.pred cube.b cube.h cube.copies cube.width → scalarIDs)



open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator CellMacro.Generator TeamContraction.JointHeader TeamContraction.ProcessorSlots
open BorderVNP.Epoch.Round

variable {extra phase deg Q scaleA scaleB scaleJ : ℕ} (scales : EpochScales S (cube.pred+1) extra)
    (b : JointSchedule.{0} scales (phase+1) deg Q scaleA scaleB scaleJ)
    (room : ReaderTallyInputsAt cube b (k+1)) (batchEq : r=stretch b.ρ (k+1)) (stateEq : s=stretch b.σ (k+1))
    (teamsEq : R=b.physical.teamsPred (k+1)) (alpha : α=scales.α) (fraction : ξ=(scales.τ:ℝ)/5)
    (fields : RecordData (Boundary.seedState S (tapeTemplate p fit ((pairedTableParameters (k+1) s+2)*pin))
      d order position copies table words).pack.layout) {startCap : ℕ}
    (cover : (CoverScale.sites (Cube D) (d+1):ℝ) ≤ r*((k+1:ℕ):ℝ)^(9/10:ℝ))
    (small : 1+startCap ≤ TeamScales.width (k+1) (1/2:ℝ))
    (bound : PhysicalEpochs.SiteCap (Boundary.seedState S (tapeTemplate p fit ((pairedTableParameters (k+1) s+2)*pin))
      d order position copies table words).route fields true startCap) (time : T≤epochs scales.τ (k+1))
    {reserve groups capacity : ℕ}
    {gen : CellMacro.Generator.Fragment IO}
    (X : UncheckedCandidate (cube.cubeID e) gen (k+1) (b.physical.word (k+1)) (R+1)
      (pairedTableParameters (k+1) s + Fintype.card (e.Entry ⊕ TableEntry cube.pred cube.b cube.h cube.copies cube.width))
      (b.physical.tally (k+1)))
    (hdr : PositiveFields reserve cube.pred groups capacity (R+1)
      (pairedTableParameters (k+1) s + Fintype.card (e.Entry ⊕ TableEntry cube.pred cube.b cube.h cube.copies cube.width))
      (b.physical.tally (k+1)))
    (startup : Fin (R+1) → StartupArena)

local notation3 (prettyPrint := false) "counts" => signedTermCounts plan cube φ ord chart p fit W position sites edges ports table
  words good free count hp α ξ calibrated lit hd number gap
local notation3 (prettyPrint := false) "totals" => signedTermTotals plan cube φ ord chart p fit W position sites edges ports table
  words good free count hp α ξ calibrated lit hd number gap

variable (arenaBase profileBits : ℕ) (frame origin : ℕ)
local notation3 (prettyPrint := false) "charge" => S.publicProgramFactor^T*initialMass (D:=D) (k+1) r d copies header
local notation3 (prettyPrint := false) "seedCap" => DeckGrid.seedBoxCapacity (k+1) r axes d (Fintype.card (DeckGrid.Direction axes))
local notation3 (prettyPrint := false) "mark" => signedMarkedLimit copies seedCap
  ((birthWordCoefficient e+8)*(Packing.BankCharges.bound e+1)*(S.populationFactor+2)) charge
local notation3 (prettyPrint := false) "prRows" => 16*(e.count+1)
local notation3 (prettyPrint := false) "fifth" => TeamScales.width (k+1) (1/5)
local notation3 (prettyPrint := false) "fourth" => TeamScales.width (k+1) (1/4)
local notation3 (prettyPrint := false) "Bq" q => dir q cube α ξ calibrated lit hd number gap
local notation3 (prettyPrint := false) "selectedPath" => signedDecodedPath plan cube φ ord chart p fit W position sites edges ports table
  words good seeds free count hp α ξ calibrated lit hd number gap
local notation3 (prettyPrint := false) "selectedCells" q => signedAssignedCells plan p fit W position code sites edges ports table words good seeds
  free count Sum.inl num hp q cube α ξ calibrated lit hd number params arenaBase profileBits (fun _ => frame) (fun _ => origin)

local notation3 (prettyPrint := false) "labels" => ParseTable.numberedLabelEquiv ord k s
local notation3 (prettyPrint := false) "scalars" => Fintype.equivFin (scalarIDs)
local notation3 (prettyPrint := false) "gid" => (scalars) ∘ put
open Packing.DeckGrid Packing.RoutingOutputs.NativeDemands
local notation3 (prettyPrint := false) "seedBlock" => GridHosts.inputBlockWidth r (k+1) axes d
local notation3 (prettyPrint := false) "desc" => seedDescriptionWidth (k+1) r axes d (header*logWidth r (k+1)) (BottomGridBank.bodyBudget seedCap)
local notation3 (prettyPrint := false) "deliveries" => freeDirectory R r ((UniversalMachine.programPrefix p).length+(TeamContraction.cutWidth (k+1)+a))
  link tiles seedBlock ((fan S)^T*tiles) desc
local notation3 (prettyPrint := false) "arena" =>
  (CubeArena.selectedSizes arenaBase (BorderVNP.Cube.alphabet α (k+1)) ((R+1)*exterior ξ r (k+1))
    cells ((boundary S (d+1) T).edges+4*((R+1)*CoverScale.sites (Cube D) (d+1))) (deliveries).candidates
    (R+1) r (k+1) profileBits).selected cube.pred cube.b cube.h cube.copies cube.width
local notation3 (prettyPrint := false) "theTask" => SignedTaskArena.Layout.mk arena (cube.cubeID e) params

include room batchEq stateEq teamsEq alpha fraction fields cover small bound time in
/-- The original signed route and bank produce their original exponent vector
on the genuine selected machine. Each raw prefix is supplied by the issued
call setup and returns on its own finite tape. All report semantics and both
the individual and full-sum word bounds come from the original frozen term. -/
theorem signedReceived_protectedCompletion_ofPrefixFinishRuns
    (hm : 0 < m) (hr : 0 < r) (short : GridHosts.inputBlockWidth r (k+1) axes d ≤ link)
    (gpos : 0<(params).report.gadgets) (fits : ∀ z : e.Entry,(num (Sum.inl z))≤(params).report.gadgets-1)
    {cost breadth exponent steps : ℕ}
    (scale : SignedReceivedScale fifth fourth (params).report.countWidth (params).report.gadgets charge
      (max (tableLimit e) (max 8 seedCap)) mark (cost*(logWidth r (k+1)+1)^exponent))
    (scheduled : PrivateCellBudgetAt 3076 (tableLimit e) (breadth+10) (steps+1) prRows cost exponent (k+1) r)
    (idBound : ((params).report.gadgets-1).size+1≤breadth*(logWidth r (k+1)+1)^steps)
    (wordEq : (params).report.countWidth=b.physical.word (k+1))
    (raw : Fin ((pairedTableParameters (k+1) s+2)*pin) → Bool) (q : Hist)
    (v : {v : (Bq q).Route cube.width × (Bq q).Bank // (Bq q).Guard (banks raw) v})
    (same : X.UsesRows ((selectedCells q) (banks raw) v.val (Bq q).owner))
    (pubFrame : ∀ (ok : ∀ u c,c∈X.assigned u → c.Passing (b.physical.word (k+1)) (k+1)) cc t,
      frame=((X.team (DiagonalTallyCellReports.canonicalReports X.assigned ok) cc t).pub 0).val)
    (run : plan.signedReceivedPrefixRuns p fit W position params labels scalars sites edges ports table words
      good seeds free count Sum.inl hp q cube α ξ calibrated lit hd number arenaBase profileBits frame origin
      (banks raw) v.val.1 v.val.2 X hdr same.1 same.2 startup gid pubFrame) :
    let path := selectedPath raw q v
    ∃ H : X.Completion hdr,H.rows=counts raw path ∧ (∀ proposal t,H.Protected X proposal t theTask (startup t)) ∧
      ∀ c,(∑ t,H.rows t c)=totals raw path c := by
  let path := selectedPath raw q v
  have eq := plan.signedDecodedTerm_sameCounts cube φ ord chart p fit W position sites edges ports table
    words good seeds free count hp α ξ calibrated lit hd number gap q raw v
  have word := (plan.signedTermCounts_word cube φ ord chart p fit W position sites edges ports table words
    good free count hp α ξ calibrated lit hd number gap scales b room batchEq stateEq teamsEq alpha fraction
    fields cover small bound time raw path).1
  have hw : b.physical.tally (k+1)=b.physical.word (k+1) :=
    (b.sizes (Nat.succ_pos k)).2.2.2.1.trans (b.sizes (Nat.succ_pos k)).2.2.1.symm
  rw [hw] at word
  have returned := plan.signedReceived_returnedFinish p fit W position params labels scalars sites edges ports
    table words good seeds free count Y chart.preserves_paid Sum.inl hp q cube α ξ calibrated lit hd number
    arenaBase profileBits frame origin (banks raw) (fun _ => (theTask).after.reportCursor) v.val.1 v.val.2
    X hdr same.1 same.2 startup gid pubFrame run (counts raw path) eq word
  exact plan.signedReceived_protectedCompletion cube φ ord chart p fit W position sites edges ports table words
    good seeds free count hp α ξ calibrated lit hd number params scales b room batchEq stateEq teamsEq alpha
    fraction fields cover small bound time X hdr (fun _ => theTask) startup arenaBase profileBits
    (fun _ => frame) (fun _ => origin) hm hr short gpos fits scale scheduled idBound wordEq raw q v
    (Bq q).owner (Bq q).owner_site same returned

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI

import OAI.Computability.BorderVNP.DiagonalSelectedSubstantiatedWidth

/-! # The completion statement at a fixed original source and layout -/

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
-- These local notations are also used in later section-variable types.
set_option hygiene false
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
local notation3 (prettyPrint := false) "dir" => signedCoreDirectory plan p fit W position code sites edges ports table words
  good seeds free count Sum.inl num hp


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
    {digits : ℕ}
    (X : UncheckedCandidate (cube.cubeID e) gen (k+1) (b.physical.word (k+1)) (R+1)
      (pairedTableParameters (k+1) s + Fintype.card (e.Entry ⊕ TableEntry cube.pred cube.b cube.h cube.copies cube.width))
      digits)
    (hdr : PositiveFields reserve cube.pred groups capacity (R+1)
      (pairedTableParameters (k+1) s + Fintype.card (e.Entry ⊕ TableEntry cube.pred cube.b cube.h cube.copies cube.width))
      digits)
    (startup : Fin (R+1) → StartupArena)

variable (arenaBase profileBits : ℕ) (frame origin : ℕ)
local notation3 (prettyPrint := false) "charge" => S.publicProgramFactor^T*initialMass (D:=D) (k+1) r d copies header
local notation3 (prettyPrint := false) "seedCap" => DeckGrid.seedBoxCapacity (k+1) r axes d (Fintype.card (DeckGrid.Direction axes))
local notation3 (prettyPrint := false) "mark" => signedMarkedLimit copies seedCap
  ((birthWordCoefficient e+8)*(Packing.BankCharges.bound e+1)*(S.populationFactor+2)) charge
local notation3 (prettyPrint := false) "prRows" => 16*(e.count+1)
local notation3 (prettyPrint := false) "fifth" => TeamScales.width (k+1) (1/5)
local notation3 (prettyPrint := false) "fourth" => TeamScales.width (k+1) (1/4)
local notation3 (prettyPrint := false) "Bq" q => dir q cube α ξ calibrated lit hd number gap
local notation3 (prettyPrint := false) "selectedCells" q => signedAssignedCells plan p fit W position code sites edges ports table words good seeds
  free count Sum.inl num hp q cube α ξ calibrated lit hd number params arenaBase profileBits (fun _ => frame) (fun _ => origin)

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

variable (digitsEq : digits=b.physical.tally (k+1))
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
    (installed : SignedTaskArena.Layout) (layoutEq : installed=theTask)

set_option hygiene true

local notation3 (prettyPrint := false) "completionAt" =>
  @signedSubstantiatedAtWidth D m _ K F _ _ e S R r pin link k d a regs rw ec width s copies T header work plan cube φ ord qchar common
  chart p fit order W position ns ne np sites edges ports table words good seeds free count hp α ξ calibrated
  lit hd cells number reportArena dirs bundles marked expBits reportWord headerSize body extra phase deg Q
  scaleA scaleB scaleJ scales b room batchEq stateEq teamsEq alpha fraction fields startCap cover small bound
  time reserve groups capacity gen digits X hdr startup arenaBase profileBits frame origin digitsEq hm hr short
  gpos fits cost breadth exponent steps scale scheduled idBound wordEq raw q v same pubFrame installed layoutEq

/-- The genuine subtotal run at these reports produces an original protected
completion with the recovered per-team rows and all monomial column sums. -/
def SubstantiatedRequest : Prop := type_of% (completionAt)

include room batchEq stateEq teamsEq alpha fraction fields startCap cover small bound time digitsEq hm hr short gpos
  fits cost breadth exponent steps scale scheduled idBound wordEq layoutEq in
/-- Apply the calibrated completion theorem after choosing its candidate,
native header, report assignment, and installed reader layout. -/
theorem substantiatedRequest :
    @SubstantiatedRequest D m _ K F _ _ e S R r pin link k d a regs rw ec width s copies T header work plan cube φ ord qchar common
  chart p fit order W position ns ne np sites edges ports table words good seeds free count hp α ξ calibrated
  lit hd cells number reportArena dirs bundles marked expBits reportWord headerSize body extra phase deg Q
  scaleA scaleB scaleJ scales b reserve groups capacity gen digits X hdr startup arenaBase profileBits frame
  origin raw q v same pubFrame installed :=
  completionAt

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI

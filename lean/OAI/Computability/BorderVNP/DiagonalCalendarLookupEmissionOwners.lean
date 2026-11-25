import OAI.Computability.BorderVNP.DiagonalPublishedOwnerRead
import OAI.Computability.BorderVNP.DiagonalIssuedEnumerations
import OAI.Computability.BorderVNP.DiagonalSelectedCalendarObservation
import OAI.Computability.BorderVNP.DiagonalOriginalReportFrameTerm
import OAI.Computability.BorderVNP.DiagonalSelectedLookupFrameFields
import OAI.Computability.BorderVNP.DiagonalReportOpeningDomainTerm
import OAI.Computability.BorderVNP.DiagonalCalendarLookupReportTests
import OAI.Computability.BorderVNP.DiagonalCalendarLookupPacketLabels
import OAI.Computability.BorderVNP.DiagonalReturnedOwnerSourceWords
import OAI.Computability.BorderVNP.DiagonalCalendarLookupSourceOwners

/-! # The native receiving team of each cell on a proposed lookup report -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Diagonal.ExternalSew Cover Packing Packing.DeckGrid Crossing Branch Epoch PackedHistoryCircuit
open PackedHistoryCircuit.Normalized SelectedSchedule EnrichedOuter TeamScales TeamContraction ProcessorSlots
open VPVNP ParseBatch ParseBatchVerifier Prewire VPVNP.ParseGrammar
open FieldProcessor RoutingISA RoutingISA.Evaluator RoutingISA.Transmission
open GeometryAdvice GeometryFrameEncoding RoutingISA.Pins VPVNP.BurstRAM RoutingISA.CompactMachine TeamSite
open DiagonalResidueRAM ResidueEntryInput ResidueRates ResiduePins
open Diagonal.ExternalSew GridHosts
open scoped Classical BorderVNP.Epoch.Cube


open Packing.Inherited Packing.Inherited.FrozenTape Shortening.PublicCapacity BorderVNP.Epoch.Round
open ResidueIndex ResidueBox
attribute [local instance] portFintype
attribute [local irreducible] Nat.clog UniversalMachine.programPrefix logWidth prefixCapacity
  FieldProcessor.freeWidth Fintype.equivFin
set_option maxRecDepth 8200
set_option maxHeartbeats 4400000
set_option synthInstance.maxSize 4000

variable {D m : ℕ} [NeZero D] {F K : Type} [Field F] [Field K] {paid : PaidIdentity F D m}
    {S : SiteSchedule paid} {cube : FixedCube K} {extra E p Q breadth sourcePower : ℕ}
    {scales : EpochScales S (cube.pred+1) extra}
    {b : JointSchedule.{0} scales (E+1) (max (5*(E+2)) p) Q 3076 (breadth+10) (sourcePower+1)}
    {φ : K →+* F} {q : ℕ} {hm : 0 < «m»} {header C A₀ a B₀ b₀ J j coeff addr power cut : ℕ}
    {adv : ℕ → ℕ} {c charge factor l : ℕ}
    (cal : SignedCalendarAt cube b φ q hm header C A₀ a B₀ b₀ J j coeff addr power cut adv c charge factor (l+1))

local notation "r₁" => stretch b.ρ (l+1)
local notation "size₁" => stretch b.σ (l+1)
local notation "R₁" => b.physical.teamsPred (l+1)
local notation "w₁" => b.physical.word (l+1)
local notation "ξ₁" => (scales.τ:ℝ)/5
local notation "ℓ₁" => TeamScales.link (ξ₁) (R₁+1) (l+1)
local notation "ec₁" => Wires.sortExponent (block (ξ₁) (l+1))
local notation "budget₁" => adv (adviceScale b.σ b.ρ (l+1))
local notation "pins₁" => (pairedTableParameters (l+1) (size₁)+2)*(budget₁+6)
local notation "d₁" => CoverScale.initialDepth (Cube D) (r₁) (l+1)-1
local notation "axes" => Fintype.card (Cube D)
local notation "tiles" => GridHosts.tileCount axes (d₁)
local notation3 (prettyPrint := false) "order₁" => (Fintype.equivFin (Fin axes → Deck (d₁+2))).symm
local notation3 (prettyPrint := false) "geo₁" => cal.sites.choose
local notation3 (prettyPrint := false) "prog₁" => cube.signedSiteProgram paid
local notation "a₁" => FieldProcessor.freeWidth (prog₁) scales.α 32 64 (r₁) (w₁) (l+1)
local notation "extra₁" => setupWidth (w₁+1) (l+1)+(prefixCapacity (r₁) 32 64 (w₁) (l+1)+1+a₁)
local notation3 (prettyPrint := false) "tape₁" => tapeTemplate (R:=R₁) (r:=r₁) (link:=ℓ₁) (regs:=64) (w:=w₁)
  (e:=ec₁) (width:=w₁+1) (k:=l) (a:=extra₁) (prog₁) (geo₁).fits (pins₁)

variable (oper : FrozenExecutionAt cube b φ q adv c charge header (hm:=hm) (l+1)) (qpos : 1 ≤ Q)
    (position : (Fin (Fintype.card (Cube D)) → Deck (CoverScale.initialDepth (Cube D)
      (stretch b.ρ (l+1)) (l+1)-1+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
local notation "T₁" => epochs scales.τ (l+1)
local notation "copies₁" => TeamScales.width (l+1) scales.α
local notation "J₁" => (fan S)^T₁*tiles
local notation "description" => seedDescriptionWidth (l+1) (r₁) axes (d₁) (header*logWidth (r₁) (l+1))
  (BottomGridBank.bodyBudget (seedBoxCapacity (l+1) (r₁) axes (d₁) (Fintype.card (Direction axes))))
local notation "cap₁" => SeedPlan.profileReserve (r₁) (l+1)
local notation "ceiling₁" => geometryGateCeiling (8*(11920000+1500000+16008100*coeff+37)) (4*(E+2)) (r₁) (l+1)
local notation3 (prettyPrint := false) "dir₁" => freeDirectory (R₁) (r₁)
  ((tape₁).program.length+(cutWidth (l+1)+extra₁)) (ℓ₁) tiles (GridHosts.inputBlockWidth (r₁) (l+1) axes (d₁)) J₁ description

variable {ord : Fin (l+1) × Bool ≃ Fin (2*(l+1))}
    {common : CommonField paid (φ ∘ cube.table) q l (stretch b.σ (l+1)) ord}
    (chart : AdvisedBranch common) [Fact common.p.Prime] [Algebra (ZMod common.p) chart.E]
    (reader : ChosenReader chart (b.physical.teamsPred (l+1)+1) (stretch b.ρ (l+1))
      (b.physical.multBits (l+1)) (b.physical.tally (l+1)) (b.physical.word (l+1))
      (adv (adviceScale b.σ b.ρ (l+1))+6))
    (chargeFit : reader.charge ≤ c*(adv (adviceScale b.σ b.ρ (l+1))+1)^charge)


local notation3 (prettyPrint := false) "layout₁" => cal.frozenLayout chart reader chargeFit
local notation3 (prettyPrint := false) "initial₁" => reader.startupArenaWith (n:=l+1) (reg:=64)
  (prog₁) (a₁) (ℓ₁) (layout₁).header
local notation3 (prettyPrint := false) "located₁" => cal.locatedGateTable oper.grid qpos position (initial₁)
local notation3 (prettyPrint := false) "plan₁" => cal.seed.choose
local notation3 (prettyPrint := false) "W₁" => cal.frozenWitness
local notation3 (prettyPrint := false) "sites₁" => (Fintype.equivFin (((W₁).routedFine position).Site)).toEmbedding
local notation3 (prettyPrint := false) "edges₁" => (Fintype.equivFin (((W₁).routedFine position).Edge)).toEmbedding
local notation3 (prettyPrint := false) "ports₁" => (Fintype.equivFin (Fin (r₁) × Fin (publicWidth (tape₁)))).toEmbedding
local notation3 (prettyPrint := false) "number₁" => Fintype.equivFin (Cube D → Deck (EnrichedOuter.depth S (d₁+1) T₁+1))
local notation3 (prettyPrint := false) "tag₁" => ParseTable.signedLiteralCode (s:=size₁) ord
local notation3 (prettyPrint := false) "x₁" => fun _ : Unit => false

local notation3 (prettyPrint := false) "selectedTask" => cal.frozenTask oper.grid qpos position chart reader chargeFit
local notation3 (prettyPrint := false) "selectedSites" => cal.frozenSites oper.grid qpos position chart reader chargeFit
local notation3 (prettyPrint := false) "table₁" => (located₁).raw.reserve ceiling₁
local notation3 (prettyPrint := false) "directory₁" => freeDirectory R₁ r₁ (initial₁).literal ℓ₁ tiles
  (GridHosts.inputBlockWidth r₁ (l+1) axes d₁) J₁ description
local notation3 (prettyPrint := false) "fresh₁" => (initial₁).next+7*(directory₁).candidates
local notation3 (prettyPrint := false) "origin₁" =>
  Allocation.dest fresh₁ cap₁ (table₁).size (located₁).outputs w₁
local notation3 (prettyPrint := false) "P₁" => (signedProgram (cube.cubeID paid)).program
local notation3 (prettyPrint := false) "free₁" => (selectedSites).enrichedFree prog₁ P₁ (l+1) ec₁ ℓ₁
local notation3 (prettyPrint := false) "geoSeed" => ((plan₁).execute tape₁ order₁ position Unit).choose
local notation3 (prettyPrint := false) "arenaBase" =>
  Allocation.stop ((initial₁).next+7*(dir₁).candidates) cap₁ ceiling₁ (located₁).outputs w₁ w₁
open BorderVNP.Cube.Physical.NativeAssignments DiagonalTallyPacketEmit

local notation3 (prettyPrint := false) "hold₁" => cal.frozenRouteBlock chart reader chargeFit
local notation3 (prettyPrint := false) "bounds₁" => cal.frozenSpliceBounds oper.grid
local notation3 (prettyPrint := false) "leaf(" v ")" => (plan₁).frozenLeaf tape₁ order₁ position W₁ tag₁ sites₁ edges₁ ports₁ v x₁
local notation3 (prettyPrint := false) "history(" v ")" => (packHistory (leaf(v)) (plan₁).compiled.machine.epoch T₁).Index
local notation "identifiers" => paid.Entry ⊕ BorderVNP.Cube.TableEntry cube.pred cube.b cube.h cube.copies cube.width
local notation "qdim" => pairedTableParameters (l+1) size₁+Fintype.card identifiers

open JointHeader Routing RoutingISA.Evaluator.SignedPrep CellEntries
local notation3 (prettyPrint := false) "planner₁" => cal.frozenPlannerTask oper.grid qpos position chart reader chargeFit
local notation3 (prettyPrint := false) "elig(" vs "," hist ")" =>
  (plan₁).signedBroadcastAllowed prog₁ (geo₁).fits W₁ position tag₁ sites₁ edges₁ ports₁ vs
    ((geoSeed).eval x₁) (leaf(vs)).property free₁ oper.grid.count (bounds₁).2.1 hist cube scales.α ξ₁
    (bounds₁).1 (geo₁).literalSize (bounds₁).2.2 number₁ (selectedTask).p arenaBase cap₁


open Packing.RoutingOutputs RoutingISA.SignedTaskArena GeometryFrameEncoding
open VPVNP.VerifierNetwork BorderVNP.PackedHistoryCircuit

set_option cleanup.letToHave false
set_option maxRecDepth 15000
set_option maxHeartbeats 12000000

open Lean Meta Elab Term in
private def selectedOwnerObserver (inputs : Array (Name × Expr)) : TermElabM Expr := do
  let head ← mkConstWithFreshMVarLevels ``SignedPrep.CandidateReportPublication.proposedOwnersAtSource
  forallTelescope (← inferType head) fun args _ => do
    let mut values : Std.HashMap FVarId Expr := {}
    for (name, actual) in inputs do
      let some parameterExpr ← args.findM? fun v => return (← v.fvarId!.getDecl).userName == name |
        throwError "missing original owner operand {name}"
      values := values.insert parameterExpr.fvarId! actual
      unless name == `ownerAt do
        let formalType ← inferType parameterExpr
        let some c := formalType.getAppFn.constName? | throwError "expected an original report or equality"
        let some actualType ← whnfUntil (← inferType actual) c | throwError "expected original {c}"
        unless ← isDefEq formalType.getAppFn actualType.getAppFn do throwError "original owner universe mismatch"
        for formal in formalType.getAppArgs, native in actualType.getAppArgs do
          if formal.isFVar then values := values.insert formal.fvarId! native
    let mut parameters := #[]
    for x in args do
      let name := (← x.fvarId!.getDecl).userName
      if name == `u then return mkAppN head parameters
      let some value := values[x.fvarId!]? | throwError "original report did not supply parameter {name}"
      parameters := parameters.push value
    throwError "missing original receiving team"

-- Infer the native parameters once from the returned records and the two
-- equalities. The resulting operation still quantifies every possible report.
open Lean Meta Elab Term in
local elab "selectedOwnerObserver% " p:term:max o:term:max owner:term:max
    labels:term:max allocated:term:max : term => do
  selectedOwnerObserver #[ (`K, ← elabTerm p none), (`opening, ← elabTerm o none),
    (`ownerAt, ← elabTerm owner none), (`names, ← elabTerm labels none),
    (`allocated, ← elabTerm allocated none)]

private def storeEmissionOwners {P : Prop} (proof : P) : PSigma (fun Q : Prop => Q) :=
  ⟨P, proof⟩

open Lean Meta Elab Term in
local elab "storeEmissionOwners% " report:term : term => do
  let proof ← withoutErrToSorry (elabTerm report none)
  return mkApp2 (mkConst ``storeEmissionOwners) (← inferType proof) proof

private noncomputable def lookupEmissionOwners
    (values : (seedBundle (tape₁) axes d₁ (order₁) position copies₁).Tables F)
    (h : Index (Fin (Module.finrank (ZMod common.p) chart.E)) (Fin (pairedTableParameters (l+1) size₁))
      (chart.pinRadius (R₁+1) r₁))
    (i : Fin pins₁ → Bool) (hist : history(values)) (claim : Fin ((R₁+1)*(qdim)*w₁) → Bool)
    (raw : CheckedBroadcast (planner₁).cube) (allowed : (elig(values,hist)) raw.val)
    (publication : cal.LookupReportPublicationAt oper qpos position chart reader chargeFit values h i hist claim raw allowed)
    (opened : cal.LookupReportOpeningAt oper qpos position chart reader chargeFit values h i hist claim raw allowed) : PSigma (fun Q : Prop => Q) :=
  let s := cal.frozenLookupAt oper qpos position chart reader chargeFit values h i hist claim raw allowed
  let installed := originalLookupFrame% s
  let projectedOwner := issuedField% owned (issuedField% projection s)
  let labels := onReturnedCalendar% s for SignedCalendarAt.frozenLookup_packetLabel
  let owners := onReturnedCalendar% s for SignedCalendarAt.frozenLookupSourceOwners
  storeEmissionOwners% atReportOpening% (type_of% @opened) with
      operands H delivery eqTab eqRow writer runs pins recv q endRows handoff observed as AtReturn =>
    let opening : AtReturn := opened operands H delivery eqTab eqRow writer runs pins recv q endRows handoff observed
    let z := installed.replay hold₁ operands
    let exterior := z.1
    let K := originalReportEvidence% publication at [exterior]
    let observedWord := onReturnedCalendar% s for SignedCalendarAt.frozenLookupOwnerReadback at [q.val, q.property.1]
    let registered := publishedOwnerRead% observedWord via projectedOwner
    selectedOwnerObserver% K opening registered labels owners

/-- The physical owner array for every possible report and its sparse emission, on the installed
lookup replay of this calendar and the matching routed declaration. -/
theorem SignedCalendarAt.frozenLookupEmissionOwners
    (values : (seedBundle (tape₁) axes d₁ (order₁) position copies₁).Tables F)
    (h : Index (Fin (Module.finrank (ZMod common.p) chart.E)) (Fin (pairedTableParameters (l+1) size₁))
      (chart.pinRadius (R₁+1) r₁))
    (i : Fin pins₁ → Bool) (hist : history(values)) (claim : Fin ((R₁+1)*(qdim)*w₁) → Bool)
    (raw : CheckedBroadcast (planner₁).cube) (allowed : (elig(values,hist)) raw.val)
    (publication : cal.LookupReportPublicationAt oper qpos position chart reader chargeFit values h i hist claim raw allowed)
    (opened : cal.LookupReportOpeningAt oper qpos position chart reader chargeFit values h i hist claim raw allowed) :
    (lookupEmissionOwners cal oper qpos position chart reader chargeFit values h i hist claim raw allowed publication opened).1 :=
  (lookupEmissionOwners cal oper qpos position chart reader chargeFit values h i hist claim raw allowed publication opened).2

end Diagonal

end BorderVNP
end Computability
end OAI

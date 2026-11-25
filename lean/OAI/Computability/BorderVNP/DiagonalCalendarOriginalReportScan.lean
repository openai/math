import OAI.Computability.BorderVNP.DiagonalCalendarFundedEmissionOnOriginalReports
import OAI.Computability.BorderVNP.DiagonalCalendarRouteInputsOnOriginalReports
import OAI.Computability.BorderVNP.DiagonalCalendarOriginalReportOperation
import OAI.Computability.BorderVNP.DiagonalCalendarFundedSourceChart
import OAI.Computability.BorderVNP.DiagonalCalendarIssuedBareAt
import OAI.Computability.BorderVNP.DiagonalCalendarRegisteredSiteOperator
import OAI.Computability.BorderVNP.DiagonalIssuedReportNetwork
import OAI.Computability.BorderVNP.DiagonalIssuedScannerNetwork

/-! # Recorded report layouts and scan results at their actual paid addresses -/

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
local notation3 (prettyPrint := false) "selectedTask" => cal.frozenTask oper.grid qpos position chart reader chargeFit
local notation3 (prettyPrint := false) "table₁" => (located₁).raw.reserve ceiling₁
local notation "outside₁" => TeamScales.exterior (ξ₁) (r₁) (l+1)
local notation3 (prettyPrint := false) "directory₁" => freeDirectory R₁ r₁ (initial₁).literal ℓ₁ tiles
  (GridHosts.inputBlockWidth r₁ (l+1) axes d₁) J₁ description
local notation3 (prettyPrint := false) "fresh₁" => (initial₁).next+7*(directory₁).candidates
open BorderVNP.Cube.Physical.NativeAssignments DiagonalTallyPacketEmit

local notation3 (prettyPrint := false) "addresses" => reader.deployedReferenceAddresses initial₁ selectedTask directory₁
  (adviceOffsetWith prog₁ r₁ 32 64 w₁ (l+1)) outside₁ fresh₁ cap₁ (table₁).size (located₁).outputs w₁
local notation3 (prettyPrint := false) "hold₁" => cal.frozenRouteBlock chart reader chargeFit
local notation3 (prettyPrint := false) "boots₁" => cal.frozenSites_boots oper.grid qpos position chart reader chargeFit hold₁
local notation3 (prettyPrint := false) "fullPin" h => (boxPinCodec (pairedTableParameters (l+1) size₁) reader.rankFits reader.boxFits).encode h

open RoutingISA.Evaluator.ScheduleClock TeamContraction.JointHeader
open CellMacro.Generator

/- Apply a report consumer using the exact port enumeration carried in the
actual funded packet, together with its original schema types. -/
open Lean Meta

local elab "originalBillingOn%" source:term:max operative:term:max : term => do
  let checks ← Lean.Elab.Term.elabTerm source none
  let execution ← Lean.Elab.Term.elabTerm operative none
  forallBoundedTelescope (←inferType checks) (some 3) fun _ result => do
    let some op ← whnfUntil result ``SignedCalendarAt.FrozenRouteChecks | throwError "expected original route"
    let args:=op.getAppArgs
    let rate ← mkProjection execution `post
    return mkAppN (←mkConstWithLevelParams ``SignedCalendarAt.chargeReportOnOriginal)
      (args.extract 0 (args.size-3) ++ #[rate,checks])

local elab "atReturnedLayout%" receiver:term:max layout:term:max : term => do
  let pay ← Lean.Elab.Term.elabTerm receiver none
  let chart ← Lean.Elab.Term.elabTerm layout none
  let some given ← whnfUntil (←inferType chart) ``Eq | throwError "expected the earned chart"
  let target ← forallBoundedTelescope (←inferType pay) (some 14) fun vars _ => do
    let some field ← vars.findM? (fun x=>return (←x.fvarId!.getDecl).userName==`layout)
      | throwError "expected a layout in the actual payer"
    let some fixed ← whnfUntil (←inferType field) ``Eq | throwError "expected the layout equality"
    return fixed.getAppArgs.back!
  let equality ← mkEq given.getAppArgs[1]! target
  return mkApp2 (mkConst ``id [.zero]) equality chart

local elab "originalReturnedPrefix%" source:term:max : term => do
  let checks ← Lean.Elab.Term.elabTerm source none
  forallBoundedTelescope (← inferType checks) (some 3) fun _ result => do
    let some checked ← whnfUntil result ``SignedCalendarAt.FrozenRouteChecks | throwError "expected the returned route"
    let raw := checked.getAppArgs
    return mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.issuedBareTupleAtOfCandidates)
      ((raw.extract 0 (raw.size-3)).push checks)

local elab "returnedFieldDomain%" rule:term:max : term => do
  SignedCalendarAt.nextIssuedInput (← Lean.Elab.Term.elabTerm rule none)

set_option cleanup.letToHave false in
set_option maxRecDepth 18000 in
set_option maxHeartbeats 12000000 in
/-- Recover the input chart from the team whose restored field produced this report. -/
private noncomputable def layoutFromOriginalLookup
    (values : (seedBundle (tape₁) axes d₁ (order₁) position copies₁).Tables F)
    (h : Index (Fin (Module.finrank (ZMod common.p) chart.E)) (Fin (pairedTableParameters (l+1) size₁))
      (chart.pinRadius (R₁+1) r₁))
    (replay : ∀ i hist claim raw allowed,
      cal.LookupReportsAt oper qpos position chart reader chargeFit values h i hist claim raw allowed) : PSigma fun result : Prop => result :=
  let checks := cal.routeInputsOnOriginalReports oper qpos position chart reader chargeFit values h replay
  let originalTuple := originalReturnedPrefix% checks
  let nodes := (boots₁).2.choose (fullPin h)
  let payments := originalBillingOn% checks oper
  ⟨_,fun (f : returnedFieldDomain% originalTuple) (u : Fin (R₁+1)) =>
    let z := originalTuple f
    let layout := cal.frozenFundedLayoutAtIssuedControl oper.grid qpos position chart reader chargeFit u (nodes z.1 u)
    atReturnedLayout% (@payments f u) layout⟩

set_option cleanup.letToHave false in
set_option maxRecDepth 22000 in
set_option maxHeartbeats 16000000 in
/-- On each returned field, the chart of the restored team has the exact layout expected by the paid report. -/
theorem SignedCalendarAt.layoutAtOriginalReportedInputs
    (values : (seedBundle (tape₁) axes d₁ (order₁) position copies₁).Tables F)
    (h : Index (Fin (Module.finrank (ZMod common.p) chart.E)) (Fin (pairedTableParameters (l+1) size₁))
      (chart.pinRadius (R₁+1) r₁))
    (replay : ∀ i hist claim raw allowed,
      cal.LookupReportsAt oper qpos position chart reader chargeFit values h i hist claim raw allowed) :
    (layoutFromOriginalLookup cal oper qpos position chart reader chargeFit values h replay).1 :=
  (layoutFromOriginalLookup cal oper qpos position chart reader chargeFit values h replay).2

set_option cleanup.letToHave false in
set_option maxRecDepth 18000 in
set_option maxHeartbeats 12000000 in
/-- Read the three native scanner facts from the single emitted report. -/
private noncomputable def scanFromOriginalLookup
    (values : (seedBundle (tape₁) axes d₁ (order₁) position copies₁).Tables F)
    (h : Index (Fin (Module.finrank (ZMod common.p) chart.E)) (Fin (pairedTableParameters (l+1) size₁))
      (chart.pinRadius (R₁+1) r₁))
    (replay : ∀ i hist claim raw allowed,
      cal.LookupReportsAt oper qpos position chart reader chargeFit values h i hist claim raw allowed) : PSigma fun result : Prop => result :=
  let frames := cal.fundedEmissionOnOriginalReports oper qpos position chart reader chargeFit values h replay
  ⟨_,fun (f : returnedFieldDomain% frames) (u : Fin (R₁+1)) =>
    let same := cal.frozenPlannerTask_eq oper.grid qpos position chart reader chargeFit
    let attained := frames f u
    let scan := attained.2.choose_spec.choose_spec.choose_spec
    let header := issuedAtPhysicalNetwork% same (attained.1)
    let placement := issuedAtPhysicalGeometry% same (scan.2.2.1)
    let words := issuedControlsAtPhysicalNetwork% same (scan.2.2.2)
    And.intro header (And.intro placement words)⟩

set_option cleanup.letToHave false in
set_option maxRecDepth 22000 in
set_option maxHeartbeats 16000000 in
/-- The original lookup yields the reported frame, sparse geometry and all 37 native control words used at the paid addresses. -/
theorem SignedCalendarAt.scanAtOriginalReportedInputs
    (values : (seedBundle (tape₁) axes d₁ (order₁) position copies₁).Tables F)
    (h : Index (Fin (Module.finrank (ZMod common.p) chart.E)) (Fin (pairedTableParameters (l+1) size₁))
      (chart.pinRadius (R₁+1) r₁))
    (replay : ∀ i hist claim raw allowed,
      cal.LookupReportsAt oper qpos position chart reader chargeFit values h i hist claim raw allowed) :
    (scanFromOriginalLookup cal oper qpos position chart reader chargeFit values h replay).1 :=
  (scanFromOriginalLookup cal oper qpos position chart reader chargeFit values h replay).2

end Diagonal

end BorderVNP
end Computability
end OAI

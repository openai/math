import OAI.Computability.BorderVNP.DiagonalCalendarRouteInputsOnOriginalReports
import OAI.Computability.BorderVNP.DiagonalAttainedFragmentEmission
import OAI.Computability.BorderVNP.DiagonalCalendarPlannerReportGeometryInputs
import OAI.Computability.BorderVNP.DiagonalSelectedSitesAtAdmission
import OAI.Computability.BorderVNP.DiagonalCalendarCandidateOnOriginalReports
import OAI.Computability.BorderVNP.DiagonalCalendarBeforeDispatchOnOriginalReports
import OAI.Computability.BorderVNP.DiagonalCalendarRecordedEmissionInputs
import OAI.Computability.BorderVNP.DiagonalCalendarIssuedFinishAddresses

/-! # Sparse emission on an original report family -/

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
local notation3 (prettyPrint := false) "order₁" => (Fintype.equivFin (Fin axes → Deck (d₁+2))).symm
local notation3 (prettyPrint := false) "geo₁" => cal.sites.choose
local notation3 (prettyPrint := false) "prog₁" => cube.signedSiteProgram paid
local notation "a₁" => FieldProcessor.freeWidth (prog₁) scales.α 32 64 (r₁) (w₁) (l+1)
local notation "extra₁" => setupWidth (w₁+1) (l+1)+(prefixCapacity (r₁) 32 64 (w₁) (l+1)+1+a₁)
local notation3 (prettyPrint := false) "tape₁" => tapeTemplate (R:=R₁) (r:=r₁) (link:=ℓ₁) (regs:=64) (w:=w₁)
  (e:=ec₁) (width:=w₁+1) (k:=l) (a:=extra₁) (prog₁) (geo₁).fits (pins₁)

variable (oper : FrozenExecutionAt cube b φ q adv c charge header (hm:=hm) (l+1))
    (qpos : 1 ≤ Q)
    (position : (Fin (Fintype.card (Cube D)) → Deck (CoverScale.initialDepth (Cube D)
      (stretch b.ρ (l+1)) (l+1)-1+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
local notation "T₁" => epochs scales.τ (l+1)
local notation "copies₁" => TeamScales.width (l+1) scales.α
local notation "tiles" => GridHosts.tileCount axes d₁
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

open RoutingISA.Evaluator.SignedPrep _root_.OAI.Computability.BorderVNP.Cube

local notation3 (prettyPrint := false) "planner" =>
  cal.frozenPlannerTask oper.grid qpos position chart reader chargeFit
open Packing.RoutingOutputs RoutingISA.Evaluator.ScheduleClock

local notation3 (prettyPrint := false) "layout₁" => cal.frozenLayout chart reader chargeFit
local notation3 (prettyPrint := false) "initial₁" => reader.startupArenaWith (n:=l+1) (reg:=64)
  prog₁ a₁ ℓ₁ (layout₁).header
local notation3 (prettyPrint := false) "located₁" => cal.locatedGateTable oper.grid qpos position initial₁
local notation3 (prettyPrint := false) "issueDir" => freeDirectory R₁ r₁ (initial₁).literal ℓ₁ tiles
  (GridHosts.inputBlockWidth r₁ (l+1) axes d₁) J₁ description
local notation3 (prettyPrint := false) "origin₁" =>
  Allocation.dest ((initial₁).next+7*(issueDir).candidates) cap₁ ((located₁).raw.reserve ceiling₁).size
    (located₁).outputs w₁

local notation "par" => pairedTableParameters (l+1) size₁
local notation "atoms" => paid.Entry ⊕ _root_.OAI.Computability.BorderVNP.Cube.TableEntry cube.pred cube.b cube.h cube.copies cube.width
local notation "queryWidth" => Fintype.card (Board.Physical par (budget₁+6) w₁ atoms)
local notation "guessWidth" => Fintype.card (Guess (Fin par) reader.gridRank (Nat.clog 2 common.p+1) (Nat.clog 2 common.p))

/-- The allocated finish windows at the original field on the planner task itself. -/
private theorem originalPlannerAddresses :
    let t := planner
    let ctl := controlsBase origin₁ t.cube.cables t.cube.cells (dir₁).entries ((dir₁).teams*(dir₁).sites)
    t.FinishAddresses initial₁ ctl t.cube.header.profile t.cube.n t.cube.header.d t.cube.header.cap w₁ w₁
      queryWidth guessWidth reader.gates := by
  let contract (t : SignedTaskArena.Layout) :=
    t.FinishAddresses initial₁ (controlsBase origin₁ t.cube.cables t.cube.cells (dir₁).entries ((dir₁).teams*(dir₁).sites))
      t.cube.header.profile t.cube.n t.cube.header.d t.cube.header.cap w₁ w₁ queryWidth guessWidth reader.gates
  have same := (cal.frozenEarlyTask oper.grid qpos position chart reader chargeFit).symm.trans
    (cal.frozenPlannerTask_eq oper.grid qpos position chart reader chargeFit)
  exact (congrArg contract same).mp (cal.frozenIssuedFinishAddresses oper.grid qpos position chart reader chargeFit oper.post)

open Lean Elab Term in
open private atHead argumentsOf applyNamed from OAI.Computability.BorderVNP.DiagonalCalendarOriginalOwnership in
local elab "issuedReplayExterior% " observed:term:max : term => do
  let seen ← elabTerm observed none
  let claim ← atHead (← Lean.Meta.inferType seen) ``PreparationFrame.OwnedRouteOn
  let inputs ← argumentsOf claim
  let replay ← applyNamed ``PreparationFrame.replay inputs
  return mkProj ``Sigma 0 replay

open Lean Meta Elab Term in
private def applyReturnedSite (method : Name) (sites exterior team : Syntax) : TermElabM Expr := do
  let chosen ← elabTerm sites none
  let some receipt ← whnfUntil (← inferType chosen) ``PreparationFrame.SelectedLookupSites
    | throwError "expected the physically selected lookup sites"
  let atExterior ← elabTerm exterior none
  let u ← elabTerm team none
  return mkAppN (mkConst method receipt.getAppFn.constLevels!) (receipt.getAppArgs ++ #[chosen,atExterior,u])

open Lean Elab Term in
local elab "emissionSite% " sites:term:max exterior:term:max team:term:max : term =>
  applyReturnedSite ``PreparationFrame.SelectedLookupSites.returnedSite sites exterior team

open Lean Meta Elab Term in
local elab "emissionReturn% " sites:term:max exterior:term:max team:term:max : term => do
  let stages ← applyReturnedSite ``PreparationFrame.SelectedLookupSites.returnedSiteStages sites exterior team
  let observed := mkProj ``And 0 stages
  let some reached ← whnfUntil (← inferType observed) ``Exists | throwError "expected a reached report site"
  return mkAppN (mkConst ``Exists.choose_spec reached.getAppFn.constLevels!) (reached.getAppArgs.push observed)

open Lean Meta Elab Term in
/-- Reuse the selected team's complete input vector on the planner's cable and cell rectangle. -/
local elab "plannerEmissionAt% " fragment:term:max : term => do
  let proof ← elabTerm fragment none
  let some calibrated ← whnfUntil proof ``SignedCalendarAt.frozenCandidateEmissionInputs |
    throwError "expected the calibrated inputs of this report site"
  return mkAppN (mkConst ``SignedCalendarAt.frozenPlannerReportGeometryInputs calibrated.getAppFn.constLevels!) calibrated.getAppArgs

private def nativeEmissionEvidence {P : Prop} (report : P) : PSigma (fun p : Prop => p) := ⟨P,report⟩

set_option maxRecDepth 19000 in
set_option maxHeartbeats 16000000 in
set_option cleanup.letToHave false in
private noncomputable def emissionOnReports
    (values : (seedBundle (tape₁) axes d₁ (order₁) position copies₁).Tables F)
    (h : Index (Fin (Module.finrank (ZMod common.p) chart.E)) (Fin (pairedTableParameters (l+1) size₁))
      (chart.pinRadius (R₁+1) r₁))
    (reports : ∀ i hist claim raw allowed,
      cal.LookupReportsAt oper qpos position chart reader chargeFit values h i hist claim raw allowed) : PSigma (fun p : Prop => p) :=
  let checks := cal.routeInputsOnOriginalReports oper qpos position chart reader chargeFit values h reports
  let found := cal.reportedCandidateOnOriginalReports oper qpos position chart reader chargeFit values h reports
  let beforeCall := cal.beforeDispatchOnOriginalReports oper qpos position chart reader chargeFit values h reports
  let writers := nativeWritersForChecked% checks
  nativeEmissionEvidence <| fun f (u : Fin (R₁+1)) =>
    let report := found f
    let actual := report.1.choose_spec.choose_spec.some
    let seed := beforeCall f u
    let route := f.2.2.1.val
    let declared := SignedPrep.routeBroadcast (planner).cube _ route
    let honest := cal.frozenRouteAllowedForOwner oper.grid qpos position chart reader chargeFit values f.2.1
    let checked := cal.routeReadbackOnOriginalReports oper qpos position chart reader chargeFit values h reports f.1 f.2.1 f.2.2.2.1
    let lookup := selectedSitesOnRoute% checked declared honest route
    let physical := writers f
    let anchor := issuedReplayExterior% (physical.1.1)
    let site := emissionSite% lookup anchor u
    let issued := emissionReturn% lookup anchor u
    let fragment := emissionOnOriginal% (cal.frozenCandidateEmissionInputs oper.grid qpos position chart reader chargeFit oper.routing),
      u, issued.2.2.2.1, site, issued.1
    let plannerFacts := plannerEmissionAt% fragment
    let bounds := originalPlannerAddresses cal oper qpos position chart reader chargeFit
    let head := cal.frozenSites_frame oper.grid qpos position chart reader chargeFit u
    issuedFragmentOnRecordedVisit% actual (report.2) u (fragment.1) (fragment.2.1)
      (plannerFacts.2.1) (plannerFacts.2.2) (seed.1) (seed.2) bounds head

set_option maxRecDepth 19000 in
set_option maxHeartbeats 16000000 in
/-- The original report family supplies the registered report frame and its executed
sparse emission on every original field and team. The bank and memory are the
saved argument return, and all 37 control words are those of the native task. -/
theorem SignedCalendarAt.fundedEmissionOnOriginalReports
    (values : (seedBundle (tape₁) axes d₁ (order₁) position copies₁).Tables F)
    (h : Index (Fin (Module.finrank (ZMod common.p) chart.E)) (Fin (pairedTableParameters (l+1) size₁))
      (chart.pinRadius (R₁+1) r₁))
    (reports : ∀ i hist claim raw allowed,
      cal.LookupReportsAt oper qpos position chart reader chargeFit values h i hist claim raw allowed) :
    (emissionOnReports cal oper qpos position chart reader chargeFit values h reports).1 :=
  (emissionOnReports cal oper qpos position chart reader chargeFit values h reports).2

end Diagonal

end BorderVNP
end Computability
end OAI

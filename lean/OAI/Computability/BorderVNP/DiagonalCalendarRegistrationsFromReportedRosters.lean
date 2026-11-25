import OAI.Computability.BorderVNP.DiagonalCalendarRegistrationAtNativeNext
import OAI.Computability.BorderVNP.DiagonalCalendarIssuedApplication
import OAI.Computability.BorderVNP.DiagonalCalendarOriginalReportObservation
import OAI.Computability.BorderVNP.DiagonalCalendarSourceViewOnInputs
import OAI.Computability.BorderVNP.DiagonalCalendarRouteInputsOnOriginalReports
import OAI.Computability.BorderVNP.DiagonalCalendarNativeNext
import OAI.Computability.BorderVNP.DiagonalActualNativeSourceIssuanceTerm
import OAI.Computability.BorderVNP.DiagonalOriginalReportSpine
import OAI.Computability.BorderVNP.DiagonalOriginalRegisteredRosterRequest

/-! # Registering the original report with the roster returned by its sparse argument call -/

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
local notation "copies₁" => TeamScales.width (l+1) scales.α
variable {ord : Fin (l+1) × Bool ≃ Fin (2*(l+1))}
    {common : CommonField paid (φ ∘ cube.table) q l (stretch b.σ (l+1)) ord}
    (chart : AdvisedBranch common) [Fact common.p.Prime] [Algebra (ZMod common.p) chart.E]
    (reader : ChosenReader chart (b.physical.teamsPred (l+1)+1) (stretch b.ρ (l+1))
      (b.physical.multBits (l+1)) (b.physical.tally (l+1)) (b.physical.word (l+1))
      (adv (adviceScale b.σ b.ρ (l+1))+6))
    (chargeFit : reader.charge ≤ c*(adv (adviceScale b.σ b.ρ (l+1))+1)^charge)


variable [headerMinimum : Fact (8 ≤ header)]

local notation3 (prettyPrint := false) "fullPin" h => (boxPinCodec (pairedTableParameters (l+1) size₁)
  reader.rankFits reader.boxFits).encode h

open Lean Meta Elab Tactic Term in
/-- Compare the completed issuer with the full measured source in the kernel.
This keeps the shared calibrated expressions intact during the equality check. -/
local elab "registerOriginalSource " proposedProof:term : tactic => withMainContext do
  let goal ← getMainGoal
  let wanted ← getMainTarget
  let proof ← Term.elabTerm proposedProof (some wanted)
  Term.synthesizeSyntheticMVarsNoPostponing
  let proof ← instantiateMVars proof
  let wanted ← instantiateMVars wanted
  if proof.hasMVar || proof.hasSorry then throwError "incomplete original source issuance"
  let env ← getEnv
  let ctx ← instantiateLCtxMVars (← getLCtx)
  let actual ← match Kernel.check env ctx (ShareCommon.shareCommon proof) with
    | .ok result => pure result
    | .error reason => throwError "the kernel rejected the original source proof. {reason.toMessageData (← getOptions)}"
  match Kernel.isDefEq env ctx (ShareCommon.shareCommon actual) (ShareCommon.shareCommon wanted) with
  | .ok true => pure ()
  | .ok false => throwError "the issuer returned a different original prefix"
  | .error reason => throwError "the kernel could not compare the original prefixes. {reason.toMessageData (← getOptions)}"
  goal.assign proof
  replaceMainGoal []

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 16000 in
set_option cleanup.letToHave false in
private noncomputable def registrationsFromReportedRosters
    (values : (seedBundle (tape₁) axes d₁ (order₁) position copies₁).Tables F)
    (h : Index (Fin (Module.finrank (ZMod common.p) chart.E)) (Fin (pairedTableParameters (l+1) size₁))
      (chart.pinRadius (R₁+1) r₁))
    (reports : ∀ i hist claim raw allowed,
      cal.LookupReportsAt oper qpos position chart reader chargeFit values h i hist claim raw allowed) : Prop :=
  let entries := cal.frozenFrameEntries oper.grid qpos position chart reader chargeFit values
  let valid := cal.routeInputsOnOriginalReports oper qpos position chart reader chargeFit values h reports
  let run := originalCalibratedOperation% entries through values using SignedCalendarAt.frozenRegistrationAtNativeNext
    at [h,entries,valid]
  ∀ sparse measured,
    let next := cal.frozenNativeNext oper.grid qpos position chart reader chargeFit (fullPin h) measured sparse
    ∀ raw hist v,
      (originalCalibratedOperation% run through valid using SignedCalendarAt.rostersAtRegisteredSource
        at [next,raw,hist,v]) → (run next raw hist v).registrations

open Lean Meta Elab Command Tactic in
/-- Bind the measured calendar parameters once and store the shared proof term.
The named predicate contains the quantified source and roster statement. -/
local elab "originalRegistrationTheorem " target:ident " from " claim:ident " by " body:tacticSeq : command => do
  let name := (← getCurrNamespace) ++ target.getId.eraseMacroScopes
  let source ← getRef
  liftTermElabM do
    let predicate ← realizeGlobalConstNoOverloadWithInfo claim
    let info ← getConstInfo predicate
    forallTelescope info.type fun inputs _ => do
      let required := mkAppN (mkConst predicate (info.levelParams.map mkLevelParam)) inputs
      let goal ← mkFreshExprSyntheticOpaqueMVar required
      let remaining ← Tactic.run goal.mvarId! (Tactic.evalTactic body)
      unless remaining.isEmpty do throwError "the original source proof left a registration obligation"
      let value ← instantiateMVars goal
      let proof := ShareCommon.shareCommon (← mkLambdaFVars inputs value (generalizeNondepLet := false))
      let type := ShareCommon.shareCommon (← mkForallFVars inputs required (generalizeNondepLet := false))
      addDecl (.thmDecl { name, levelParams := info.levelParams, type, value := proof })
  addDeclarationRangesFromSyntax name source target
  addDocStringCore name "Each source in the original accepting rule receives a registered prefix when its actual sparse argument call supplies the roster read on that source."

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 16000 in
set_option cleanup.letToHave false in
originalRegistrationTheorem SignedCalendarAt.originalRegistrationsFromReportedRosters
    from registrationsFromReportedRosters by
  unfold registrationsFromReportedRosters
  intro entries valid run sparse measured next raw hist v funded proposed subtotal team
  let checked := originalCheckedReadback% valid using SignedCalendarAt.routeReadbackOnOriginalReports
    at [raw,hist,subtotal]
  let declared := originalCheckedDeclaration% checked.sites at v.1
  let allowed := originalCalibratedOperation% run through values using SignedCalendarAt.frozenRouteAllowedForOwner
    at [hist,v.1.val]
  let site := checked.sites declared allowed
  have reached := (checked.returned declared allowed).1
  let sourceAt := originalCalibratedOperation% valid through h using SignedCalendarAt.frozenSourceViewOnInputs
    at [raw,hist,subtotal,checked.inputs,v.1,proposed,team]
  have identified := sourceAt.restored
  have observation := originalCalibratedOperation% run through valid using SignedCalendarAt.frozenOriginalReportObservation
    at [next,raw,hist,v.1,subtotal,proposed,team]
  have roster := funded proposed subtotal team
  let axis : Fin (cube.pred+1) := 0
  have facts := originalCalibratedOperation% run through chargeFit using SignedCalendarAt.frozenIssuedApplication
    at [oper,values,hist,v.1,team,axis]
  have frame := originalCalibratedOperation% run through chargeFit using SignedCalendarAt.frozenSites_frame at [team]
  have planner := originalCalibratedOperation% run through chargeFit using SignedCalendarAt.frozenPlannerTask_eq at []
  registerOriginalSource (exactNativeSourceIssuance% site, reached, identified, observation, roster, facts, axis, frame.symm, planner)

end Diagonal

end BorderVNP
end Computability
end OAI

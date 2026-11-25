import OAI.Computability.BorderVNP.DiagonalOriginalReportSpine
import OAI.Computability.BorderVNP.DiagonalCalendarRegistrationAtNativeNext
import OAI.Computability.BorderVNP.DiagonalCalendarRegistrationsFromReportedRosters
import OAI.Computability.BorderVNP.DiagonalCalendarRosterFromOriginalStoredReports
import OAI.Computability.BorderVNP.DiagonalCalendarRouteInputsOnOriginalReports
import OAI.Computability.BorderVNP.DiagonalCalendarSiteOnStoredOriginalReports
import OAI.Computability.BorderVNP.DiagonalCalendarSuppliedOnOriginalReports
import OAI.Computability.BorderVNP.DiagonalCalendarNativeNext

/-! # Signed finishes from a single stored family of calendar reports -/

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

local notation3 (prettyPrint := false) "fullPin" h => (boxPinCodec (pairedTableParameters (l+1) size₁)
  reader.rankFits reader.boxFits).encode h

set_option maxRecDepth 14000 in
set_option maxHeartbeats 11000000 in
set_option cleanup.letToHave false in
private noncomputable def completionsOnStoredReports
    (values : (seedBundle (tape₁) axes d₁ (order₁) position copies₁).Tables F)
    (h : Index (Fin (Module.finrank (ZMod common.p) chart.E)) (Fin (pairedTableParameters (l+1) size₁))
      (chart.pinRadius (R₁+1) r₁))
    (reports : ∀ i hist claim raw allowed,
      cal.LookupReportsAt oper qpos position chart reader chargeFit values h i hist claim raw allowed)
    (stored : cal.StoredReportsAtOriginalInputs oper qpos position chart reader chargeFit values h reports) : Prop :=
  let entries := cal.frozenFrameEntries oper.grid qpos position chart reader chargeFit values
  let valid := cal.routeInputsOnOriginalReports oper qpos position chart reader chargeFit values h reports
  let register := originalCalibratedOperation% entries through values using
    SignedCalendarAt.frozenRegistrationAtNativeNext at [h,entries,valid]
  let packets := cal.siteDataOnStoredReportsAtOriginalInputs oper qpos position chart reader chargeFit
    values h reports stored
  let source := (cal.suppliedOnOriginalReports oper qpos position chart reader chargeFit values h reports packets).2
  ∀ measured,
    let next := cal.frozenNativeNext oper.grid qpos position chart reader chargeFit (fullPin h) measured source
    ∀ raw hist v, (register next raw hist v).runs

open Lean Meta Elab Term
open TeamContraction.ProcessorSlots.BootedPinStart

set_option maxRecDepth 24000
set_option maxHeartbeats 18000000
set_option cleanup.letToHave false

/-- Complete the stored-report predicate using the registration and funded roster at its own native route. -/
private def storedOriginalRunBody (expected : Expr) : MetaM Expr := do
  let expected := (← instantiateMVars expected).consumeMData
  let inputs := expected.getAppArgs
  unless expected.isAppOf ``completionsOnStoredReports && inputs.size == 53 do
    throwError "expected the original stored-report predicate"
  let registrations ← mkConstWithLevelParams ``SignedCalendarAt.originalRegistrationsFromReportedRosters
  let roster ← mkConstWithLevelParams ``SignedCalendarAt.rosterForRegistrationOnOriginalStoredReports
  forallBoundedTelescope expected (some 4) (whnfType := true) fun front requested => do
    let #[clockArg, rawArg, historyArg, routeArg] := front | throwError "expected the four original run inputs"
    let rule ← match requested.consumeMData with
      | .proj name 1 rule =>
        if name == ``OriginalReportRule then pure rule else throwError "expected the original rule"
      | runs =>
        if runs.isAppOfArity ``OriginalReportRule.runs 1 then pure runs.appArg!
        else throwError "expected the original rule's runs"
    let some register ← whnfUntil rule ``SignedCalendarAt.frozenRegistrationAtNativeNext
      | throwError "expected the original registration at the native continuation"
    let fields := register.getAppArgs
    let some next ← whnfUntil fields[fields.size - 4]! ``SignedCalendarAt.frozenNativeNext
      | throwError "expected the selected native continuation"
    let attach := mkAppN registrations (inputs.pop ++ #[next.getAppArgs.back!, clockArg, rawArg, historyArg, routeArg])
    let .forallE _ rosterType _ _ ← whnf (← inferType attach) | throwError "expected the funded roster"
    let funded ← forallBoundedTelescope rosterType (some 3) (whnfType := true) fun teamArgs _ => do
      let #[reportArg, subtotalArg, teamArg] := teamArgs | throwError "expected a report, subtotal and team"
      let atRoute := mkProj ``Prod 0 routeArg
      let paid := mkAppN roster (inputs ++ #[clockArg, rawArg, historyArg, atRoute, subtotalArg, reportArg, teamArg])
      mkLambdaFVars teamArgs (mkProj ``PLift 0 paid) (generalizeNondepLet := false)
    let run := mkApp (mkProj ``OriginalReportRule 2 rule) (mkApp attach funded)
    mkLambdaFVars front run (generalizeNondepLet := false)

private def allStoredReportRuns : TermElabM Expr := do
  let predicate ← mkConstWithLevelParams ``completionsOnStoredReports
  forallTelescopeReducing (← inferType predicate) fun args _ => do
    let expected := mkAppN predicate args
    let proof ← storedOriginalRunBody expected
    mkLambdaFVars args (← mkExpectedTypeHint proof expected) (generalizeNondepLet := false)

local elab "allStoredReportRuns%" : term => allStoredReportRuns

private noncomputable def completedStoredRuns : PSigma fun statement : Prop => statement :=
  ⟨_, allStoredReportRuns%⟩

/-- For every proposed report and subtotal, each team finishes on the recovered native prefix.
The packet and its funded roster come from the same returned report at that team. -/
theorem SignedCalendarAt.runsOnOriginalStoredReports : completedStoredRuns.1 :=
  completedStoredRuns.2

end Diagonal

end BorderVNP
end Computability
end OAI

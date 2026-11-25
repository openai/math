import OAI.Computability.BorderVNP.DiagonalCheckedFieldNativeWriter
import OAI.Computability.BorderVNP.DiagonalCalendarOriginalHostVisit
import OAI.Computability.BorderVNP.DiagonalChosenReportOnOriginalReturn
import OAI.Computability.BorderVNP.DiagonalCalendarReportCapacityTerm
import OAI.Computability.BorderVNP.DiagonalOriginalReportFrameTerm
import OAI.Computability.BorderVNP.DiagonalCalendarSuppliedHostSource
import OAI.Computability.BorderVNP.DiagonalSelectedLookupFrameFields
import OAI.Computability.BorderVNP.DiagonalCalendarRouteInputsOnOriginalReports
import OAI.Computability.BorderVNP.DiagonalRecordedOriginalHostSourceTerm
import OAI.Computability.BorderVNP.DiagonalReturnedCandidateStages
import OAI.Computability.BorderVNP.DiagonalRecordedApplicationTerm

/-! # Host words on each return of the original reports -/

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

variable [Fact (8 ≤ header)] (oper : FrozenExecutionAt cube b φ q adv c charge header (hm:=hm) (l+1))
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

open RoutingISA.Evaluator.SignedPrep _root_.OAI.Computability.BorderVNP.Cube

open Lean Meta Elab Term
private partial def reportAtHistory (model hist : Term) : TermElabM Term := do
  match model with
  | `(($m)) => reportAtHistory m hist
  | `($fn $args*) => `($fn $args* $hist)
  | _ => throwError "expected the original calendar report family"

private def stageOnOriginal (stage : Name) (report : Expr) : MetaM Expr :=
  RecordedApplication.fromEvidence stage `C #[(`C,report)] fun entries => do
    let C := entries[0]!
    let some reached ← whnfUntil (← inferType C) ``SignedPrep.ReturnedCandidateReports
      | throwError "missing the reached physical report"
    return (reached.getAppArgs.push C,reached.getAppFn.constLevels!)

local elab "originalScopedHostHistory%" checks:term:max readback:term:max room:term:max layout:term:max
    service:term:max fixed:term:max model:term:max capacity:term:max : term => do
  let lets := (← getLCtx).getFVarIds
  let operand (stx : Syntax) := do instantiateMVars (← zetaDeltaFVars (← elabTerm stx none) lets)
  let check ← operand checks
  let native ← nativeWriterOnCheckedRoutes check
  let issuer ← operand readback
  let admitted ← operand room
  let planner ← operand layout
  let upper ← operand service
  let hold ← operand fixed
  let .forallE _ fieldType _ _ ← whnf (← inferType native) | throwError "missing native returned original field"
  withLocalDeclD `originalField fieldType fun f => do
    let cluster := mkProj ``Sigma 0 f
    let registeredTuple := mkProj ``Sigma 1 f
    let hist := mkProj ``Sigma 0 registeredTuple
    let tail := mkProj ``Sigma 1 registeredTuple
    let route := mkProj ``Subtype 0 (mkProj ``Sigma 0 tail)
    let claim := mkProj ``Prod 0 (mkProj ``Sigma 1 tail)
    let checked := mkApp3 issuer cluster hist claim
    let correct := mkApp (mkApp admitted hist) route
    let plannerS ← exprToSyntax planner
    let routeS ← exprToSyntax route
    let raw ← elabTerm (← `(SignedPrep.routeBroadcast ($plannerS).cube _ $routeS)) none
    synthesizeSyntheticMVarsNoPostponing
    let raw ← instantiateMVars raw
    let selected := mkApp2 (mkProj ``CheckedRouteReadback 1 checked) raw correct
    let trueReader := mkProj ``PSigma 1 (mkAppN upper #[cluster,hist,claim,raw])
    let s ← exprToSyntax selected
    let reader ← exprToSyntax trueReader
    let finish := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenHostSourceFromOriginalWriter)
      (native.getAppArgs.push f)
    let .forallE _ callback _ _ ← whnf (← inferType finish) | throwError "missing the continuation of the original host writer"
    let earned := mkProj ``And 0 (mkApp2 (mkProj ``CheckedRouteReadback 2 checked) raw correct)
    let earnedS ← exprToSyntax earned
    let rawS ← exprToSyntax raw
    let words ← elabTerm (← `(declaredWords ($plannerS).cube _ (decodedBroadcast ($plannerS).cube ($rawS).val)
      ⟨$routeS,(decoded_routeBroadcast ($plannerS).cube _ $routeS).symm⟩)) none
    synthesizeSyntheticMVarsNoPostponing
    let ws ← exprToSyntax (← instantiateMVars words)
    let clock ← exprToSyntax hold
    let frame ← elabTerm (← `(originalLookupFrame% $s)) none
    let fr ← exprToSyntax frame
    let exterior ← elabTerm (← `((($fr).replay $clock $ws).1)) none
    let x ← exprToSyntax exterior
    let modelS ← reportAtHistory model (← exprToSyntax hist)
    let reports ← elabTerm (← `(frozenReportKAtLookup% $modelS $clock ($rawS).val $s)) none
    let reportS ← exprToSyntax reports
    let capType ← elabTerm (← `(originalReportStage% $reportS .capacity)) none
    let cap ← elabTerm (← `(calendarSiteReportCapacity% $capacity $rawS)) (some capType)
    let capS ← exprToSyntax cap
    forallBoundedTelescope callback (some 12) fun args originalResult => do
      unless args.size==12 do throwError "different native writer arity"
      let v ← args.mapM exprToSyntax
      let candidate ← elabTerm (← `(chosenReportOnOriginalReturn% $earnedS $ws
        $(v[0]!) $(v[1]!) $(v[2]!) $(v[3]!) $(v[4]!) $(v[5]!) $(v[6]!) $(v[7]!)
        $(v[8]!) $(v[9]!) $(v[10]!) $(v[11]!))) none
      let publication ← exprToSyntax (← stageOnOriginal ``SignedPrep.ReturnedCandidateReports.toPublication candidate)
      let opening ← exprToSyntax (← stageOnOriginal ``SignedPrep.ReturnedCandidateReports.toOpening candidate)

      let receiver ← elabTerm (← `(applyOriginalHostOnReplay% $reader $s $x at
        [$ws, $(v[0]!), $(v[1]!), $(v[2]!), $(v[3]!), $(v[4]!), $(v[5]!), $(v[6]!), $(v[7]!),
         $(v[8]!), $(v[9]!), $(v[10]!), $(v[11]!), $publication,
         originalReportEvidence% $capS at [$x, ($(v[8]!)).val], $opening])) none
      synthesizeSyntheticMVarsNoPostponing
      forallBoundedTelescope (← inferType receiver) (some 2) fun premises result => do
        unless premises.size == 2 && (← isDefEq result originalResult) do
          throwError "the retained host words differ from the original writer's result"
      let original ← instantiateMVars (← mkLambdaFVars (#[f] ++ args) receiver)
      let statement ← inferType original
      let propositions := mkSort .zero
      let identity := mkLambda `p .default propositions (.bvar 0)
      return mkAppN (mkConst ``PSigma.mk [.ofNat 1,.zero]) #[propositions,identity,statement,original]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 14000000 in
set_option cleanup.letToHave false in
/-- Reconstruct the routed host words from the same chosen candidate and its full original
writer. The report publication, capacity and opening all belong to that return. -/
noncomputable def SignedCalendarAt.hostAtHistoryOnOriginalReports
    (values : (seedBundle (tape₁) axes d₁ (order₁) position copies₁).Tables F)
    (h : Index (Fin (Module.finrank (ZMod common.p) chart.E)) (Fin (pairedTableParameters (l+1) size₁))
      (chart.pinRadius (R₁+1) r₁))
    (reports : ∀ i hist claim raw allowed,
      cal.LookupReportsAt oper qpos position chart reader chargeFit values h i hist claim raw allowed) :
    PSigma (fun p : Prop => p) := by
  let actual := cal.routeInputsOnOriginalReports oper qpos position chart reader chargeFit values h reports
  exact originalScopedHostHistory% actual
    (cal.routeReadbackOnOriginalReports oper qpos position chart reader chargeFit values h reports)
    (cal.frozenRouteAllowedForOwner oper.grid qpos position chart reader chargeFit values)
    (cal.frozenPlannerTask oper.grid qpos position chart reader chargeFit)
    (cal.frozenHostSourceOfSites oper qpos position chart reader chargeFit values h)
    (cal.frozenRouteBlock chart reader chargeFit)
    (cal.frozenReportK oper.grid qpos position chart reader chargeFit values)
    (cal.frozenSiteReportCapacity oper qpos position chart reader chargeFit)


end Diagonal

end BorderVNP
end Computability
end OAI

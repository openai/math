import OAI.Computability.BorderVNP.DiagonalCalendarOriginalReportHostHistory
import OAI.Computability.BorderVNP.DiagonalCalendarHostSetupOnOriginalReports
import OAI.Computability.BorderVNP.DiagonalCalendarOriginalHostVisit
import OAI.Computability.BorderVNP.DiagonalCalendarOriginalOwnedHostWords
import OAI.Computability.BorderVNP.DiagonalCalendarRouteInputsOnOriginalReports
import OAI.Computability.BorderVNP.DiagonalCheckedFieldNativeWriter

namespace OAI
namespace Computability
namespace BorderVNP

set_option autoImplicit false

/-! # Host words on the original reports of a signed calendar -/

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

local notation3 (prettyPrint := false) "frameEntries(" vs ")" =>
  cal.frozenFrameEntries oper.grid qpos position chart reader chargeFit vs

open RoutingISA.Evaluator.SignedPrep _root_.OAI.Computability.BorderVNP.Cube

open Lean Meta Elab Term in
local elab "actualOriginalHostAt%" checks:term:max field:term:max history:term:max
    reached:term:max : term => do
  let checked ← elabTerm checks none
  let original ← elabTerm field none
  let native ← nativeWriterOnCheckedRoutes checked
  let finish := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenHostSourceFromOriginalWriter)
    (native.getAppArgs.push original)
  let read := mkApp (← elabTerm history none) original
  let atTeam := mkApp (← elabTerm reached none) original
  let .forallE _ target _ _ ← whnf (← inferType finish) | throwError "missing original writer continuation"
  withLetDecl `reachedOriginalHost (← inferType atTeam) atTeam fun physical => do
    let (fits,heads) ← forallBoundedTelescope (← inferType physical) (some 1) fun us _ => do
      unless us.size==1 do throwError "missing original team"
      let state := mkApp physical us[0]!
      let fit := mkProj ``And 0 state
      let header := mkProj ``And 1 state
      return (← mkLambdaFVars us fit,← mkLambdaFVars us header)
    let callback ← forallBoundedTelescope target (some 12) fun observations _ => do
      unless observations.size==12 do throwError "expected the twelve original writer operands"
      mkLambdaFVars observations (mkAppN read ((observations.push fits).push heads))
    mkLetFVars #[physical] (mkApp finish callback) (generalizeNondepLet:=false)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 14000000 in
set_option cleanup.letToHave false in
/-- Reconstruct the routed host words from the same chosen candidate and its full original
writer. The report publication, capacity and opening all belong to that return. -/
noncomputable def SignedCalendarAt.fundedHostSourceOnOriginalReports
    (values : (seedBundle (tape₁) axes d₁ (order₁) position copies₁).Tables F)
    (h : Index (Fin (Module.finrank (ZMod common.p) chart.E)) (Fin (pairedTableParameters (l+1) size₁))
      (chart.pinRadius (R₁+1) r₁))
    (reports : ∀ i hist claim raw allowed,
      cal.LookupReportsAt oper qpos position chart reader chargeFit values h i hist claim raw allowed) :
    PLift (cal.OriginalOwnedHostWords oper.grid qpos position chart reader chargeFit values h frameEntries(values)
      (cal.routeInputsOnOriginalReports oper qpos position chart reader chargeFit values h reports)) := by
  let checks := cal.routeInputsOnOriginalReports oper qpos position chart reader chargeFit values h reports
  let captured := (cal.hostAtHistoryOnOriginalReports oper qpos position chart reader chargeFit values h reports).2
  let physical := (cal.hostSetupOnOriginalReports oper qpos position chart reader chargeFit values h reports).2
  refine ⟨?_⟩
  intro f
  let result := actualOriginalHostAt% checks f (@captured) (@physical)
  run_tac
    let goal ← Lean.Elab.Tactic.getMainGoal
    goal.withContext do
      goal.assign (← Lean.Meta.getFVarFromUserName `result)
      Lean.Elab.Tactic.replaceMainGoal []

end Diagonal

end BorderVNP
end Computability
end OAI

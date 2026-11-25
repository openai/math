import OAI.Computability.BorderVNP.DiagonalOriginalStoredPacketValue
import OAI.Computability.BorderVNP.DiagonalCalendarStoredOriginalReportFamily

/-! # The entire original reported call, with its original issued and saved facts -/

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

variable (oper : FrozenExecutionAt cube b φ q adv c charge header (hm:=hm) (l+1)) (qpos : 1 ≤ Q)
    (position : (Fin (Fintype.card (Cube D)) → Deck (CoverScale.initialDepth (Cube D)
      (stretch b.ρ (l+1)) (l+1)-1+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
variable {ord : Fin (l+1) × Bool ≃ Fin (2*(l+1))}
    {common : CommonField paid (φ ∘ cube.table) q l (stretch b.σ (l+1)) ord}
    (chart : AdvisedBranch common) [Fact common.p.Prime] [Algebra (ZMod common.p) chart.E]
    (reader : ChosenReader chart (b.physical.teamsPred (l+1)+1) (stretch b.ρ (l+1))
      (b.physical.multBits (l+1)) (b.physical.tally (l+1)) (b.physical.word (l+1))
      (adv (adviceScale b.σ b.ρ (l+1))+6))
    (chargeFit : reader.charge ≤ c*(adv (adviceScale b.σ b.ρ (l+1))+1)^charge)

variable [Fact (8 ≤ header)]

private abbrev inputOf {α : Sort*} {β : α → Sort*} (_ : (x : α) → β x) := α

local notation3 (prettyPrint := false) "sourceOnReports" =>
  cal.fundedGeometryOnOriginalReports oper qpos position chart reader chargeFit

open Lean Meta Elab Term in
local elab "packetAtStoredSite%" issuer:ident placement:ident field:ident team:ident original:term:max : term => do
  let ii ← elabTerm issuer none
  let place ← elabTerm placement none
  let f ← elabTerm field none
  let u ← elabTerm team none
  let chosen ← elabTerm original none
  let hist := mkProj ``Sigma 0 (mkProj ``Sigma 1 f)
  SignedCalendarAt.originalStoredPacketValue ii (mkApp place hist) f u chosen

set_option maxRecDepth 24000 in
set_option maxHeartbeats 24000000 in
set_option cleanup.letToHave false in
/-- Each stored report itself supplies the sparse native call, the original owner
and logical reads, and the saved placement used by the calibrated acquisition. -/
noncomputable def SignedCalendarAt.siteDataOnStoredReportsAtOriginalInputs
    (values : inputOf (sourceOnReports)) (h : inputOf ((sourceOnReports) values))
    (reports : inputOf ((sourceOnReports) values h))
    (stored : cal.StoredReportsAtOriginalInputs oper qpos position chart reader chargeFit values h reports) :
    inputOf (cal.suppliedOnOriginalReports oper qpos position chart reader chargeFit values h reports) :=
  let issuer := cal.suppliedOnOriginalReports oper qpos position chart reader chargeFit values h reports
  let placement := cal.frozenOriginalPlacement_iff oper.grid qpos position chart reader chargeFit values
  fun f u => packetAtStoredSite% issuer placement f u (stored f u)

end Diagonal

namespace Diagonal.SignedCalendarAt
open Lean Meta Elab Term

private def receivedStoredNative : MetaM Expr := do
  let data ← mkConstWithLevelParams ``siteDataOnStoredReportsAtOriginalInputs
  let mut ty ← inferType data
  let mut scope := 0
  while ty.isForall do
    scope := scope+1
    if ty.bindingName!.eraseMacroScopes == `stored then break
    ty := ty.bindingBody!
  forallBoundedTelescope (← inferType data) (some scope) fun inputs remaining => do
    unless !inputs.isEmpty && (← inputs.back!.fvarId!.getUserName).eraseMacroScopes == `stored do
      throwError "expected the calibrated inputs and their stored report family"
    forallBoundedTelescope remaining (some 2) fun sites _ => do
      let current := mkAppN inputs.back! sites
      let original ← storedReportAtOriginalSite current
      let launch ← mkProjection (mkProj ``Subtype 0 original) `launch
      let native ← mkProjection launch `native
      let packet := mkAppN data (inputs ++ sites)
      let eq ← mkEq (mkProj ``Sigma 0 packet) native
      let proof := mkApp2 (mkConst ``id [.zero]) eq (← mkEqRefl native)
      mkLambdaFVars (inputs ++ sites) proof

set_option maxRecDepth 26000
set_option maxHeartbeats 18000000

local elab "nativeOfTheSuppliedStoredReport%" : term => do inferType (← receivedStoredNative)

/-- Equality to the native launch in the same stored physical report
for each choice of the original field tuple and team. -/
abbrev NativeAtTheOriginalStoredInputs : Prop := nativeOfTheSuppliedStoredReport%

/-- The physical packet retains the native call actually issued in its source report. -/
theorem siteDataOnStoredReportsAtOriginalInputs_native : NativeAtTheOriginalStoredInputs := by
  run_tac
    (← Lean.Elab.Tactic.getMainGoal).assign (← receivedStoredNative)
    Lean.Elab.Tactic.replaceMainGoal []

end Diagonal.SignedCalendarAt

end BorderVNP
end Computability
end OAI

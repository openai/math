import OAI.Computability.BorderVNP.DiagonalRecordedApplicationTerm
import OAI.Computability.BorderVNP.DiagonalRegisteredHostPrefix
import OAI.Computability.BorderVNP.DiagonalRoutedOriginalOwnerWords
import OAI.Computability.BorderVNP.DiagonalCalendarRouteInputsOnOriginalReports
import OAI.Computability.BorderVNP.DiagonalCalendarOwnerAdmission
import OAI.Computability.BorderVNP.DiagonalCheckedFieldNativeWriter
import OAI.Computability.BorderVNP.DiagonalCheckedReportOnRoute

/-! # The original submitted report reads its frozen private bundle at the issued host -/

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


private def storeOriginalHost {P : Prop} (proof : P) : PSigma (fun Q : Prop => Q) :=
  ⟨P,proof⟩

open Lean Meta Elab Term in
private def originalHostArguments (certificate seen same : Expr) : MetaM (Array Expr × List Level) := do
  let some report ← whnfUntil (← inferType certificate) ``PreparationFrame.CandidateReportsOnReplay
    | throwError "expected the reports on the original replay"
  let some observation ← whnfUntil (← inferType seen) ``PreparationFrame.OwnedRouteOn
    | throwError "expected the original observed writer"
  let some equality ← whnfUntil (← inferType same) ``Eq | throwError "expected the visited scan"
  let some visits ← whnfUntil equality.getAppArgs[1]! ``PinStart.ownedVisits
    | throwError "expected the earlier owner scan's actual starts"
  return (report.getAppArgs ++ observation.getAppArgs ++ visits.getAppArgs ++
    #[equality.getAppArgs[2]!, certificate, seen, same], report.getAppFn.constLevels!)

open Lean Meta Elab Term in
/-- Apply the native host observation to the exact packet and visits of this return. -/
local elab "originalReportHostAt%" certificate:term:max seen:term:max same:term:max team:term:max : term => do
  let supplied := #[(`K, ← elabTerm certificate none), (`seen, ← elabTerm seen none),
    (`same, ← elabTerm same none)]
  let op ← RecordedApplication.fromEvidence
    ``PreparationFrame.CandidateReportsOnReplay.hostAtRegisteredVisit `seen supplied
    fun args => originalHostArguments args[0]! args[1]! args[2]!
  return mkApp op (← elabTerm team none)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
set_option cleanup.letToHave false in
private noncomputable def originalReportHost
    (values : (seedBundle (tape₁) axes d₁ (order₁) position copies₁).Tables F)
    (h : Index (Fin (Module.finrank (ZMod common.p) chart.E)) (Fin (pairedTableParameters (l+1) size₁))
      (chart.pinRadius (R₁+1) r₁))
    (reports : ∀ i hist claim raw allowed,
      cal.LookupReportsAt oper qpos position chart reader chargeFit values h i hist claim raw allowed) : PSigma (fun P : Prop => P) :=
  let checks := cal.routeInputsOnOriginalReports oper qpos position chart reader chargeFit values h reports
  storeOriginalHost <| fun (f : nativeCheckedFieldType% checks) (u : Fin (R₁+1)) =>
    let aligned := nativeWriterForCheckedField% checks f
    let route := f.2.2.1.val
    let checked := cal.routeReadbackOnOriginalReports oper qpos position chart reader chargeFit values h reports f.1 f.2.1 f.2.2.2.1
    let honest := cal.frozenRouteAllowedForOwner oper.grid qpos position chart reader chargeFit values f.2.1
    let declared := SignedPrep.routeBroadcast (cal.frozenPlannerTask oper.grid qpos position chart reader chargeFit).cube _ route
    let returned := returnedReportOnRoute% checked declared honest route
    let hosted := originalReportHostAt% returned (aligned.1.1) (aligned.1.2) u
    SignedPrep.hostedAtOwnerWords (team:=u.val) hosted aligned.2.2

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
/-- This exact registered history visits the physically stored original site at the
actual receiver, using the publication retained together with its registered scan. -/
theorem SignedCalendarAt.fundedHostOnOriginalReports
    (values : (seedBundle (tape₁) axes d₁ (order₁) position copies₁).Tables F)
    (h : Index (Fin (Module.finrank (ZMod common.p) chart.E)) (Fin (pairedTableParameters (l+1) size₁))
      (chart.pinRadius (R₁+1) r₁))
    (reports : ∀ i hist claim raw allowed,
      cal.LookupReportsAt oper qpos position chart reader chargeFit values h i hist claim raw allowed) :
    (originalReportHost cal oper qpos position chart reader chargeFit values h reports).1 :=
  (originalReportHost cal oper qpos position chart reader chargeFit values h reports).2

end Diagonal

end BorderVNP
end Computability
end OAI

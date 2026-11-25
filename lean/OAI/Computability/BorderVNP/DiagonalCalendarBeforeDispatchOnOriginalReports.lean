import OAI.Computability.BorderVNP.DiagonalAttainedReportOperands
import OAI.Computability.BorderVNP.DiagonalCalendarCandidateOnOriginalReports

/-! # Allocated report rows on the original registered candidate before sparse emission -/

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
attribute [local irreducible] stretch Nat.clog UniversalMachine.programPrefix logWidth prefixCapacity
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

local notation "R₁" => b.physical.teamsPred (l+1)

variable (oper : FrozenExecutionAt cube b φ q adv c charge header (hm:=hm) (l+1))
    (qpos : 1 ≤ Q)
    (position : (Fin (Fintype.card (Cube D)) → Deck (CoverScale.initialDepth (Cube D)
      (stretch b.ρ (l+1)) (l+1)-1+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
variable {ord : Fin (l+1) × Bool ≃ Fin (2*(l+1))}
    {common : CommonField paid (φ ∘ cube.table) q l (stretch b.σ (l+1)) ord}
    (chart : AdvisedBranch common) [Fact common.p.Prime] [Algebra (ZMod common.p) chart.E]
    (reader : ChosenReader chart (b.physical.teamsPred (l+1)+1) (stretch b.ρ (l+1))
      (b.physical.multBits (l+1)) (b.physical.tally (l+1)) (b.physical.word (l+1))
      (adv (adviceScale b.σ b.ρ (l+1))+6))
    (chargeFit : reader.charge ≤ c*(adv (adviceScale b.σ b.ρ (l+1))+1)^charge)


open RoutingISA.Evaluator.SignedPrep

private def retainOriginalRows {P : Prop} (prepared : P) : PSigma (fun goal : Prop => goal) :=
  ⟨P,prepared⟩

set_option maxRecDepth 18000 in
set_option maxHeartbeats 12000000 in
set_option cleanup.letToHave false in
private noncomputable def SignedCalendarAt.originalRowsOnReports : PSigma (fun goal : Prop => goal) :=
  let reports := cal.reportedCandidateOnOriginalReports oper qpos position chart reader chargeFit
  retainOriginalRows <| fun values h reportsAt f (u : Fin (R₁+1)) =>
    let report := reports values h reportsAt f
    let actual := report.1.choose_spec.choose_spec.some
    preparedOnAttainedOwner% actual (report.2) u

/-- Given all original report observations for the field, each receiving team has
its allocated native report input and agreement with the routed source cells. -/
theorem SignedCalendarAt.receivedBeforeDispatchOnOriginalReports :
    (cal.originalRowsOnReports oper qpos position chart reader chargeFit).1 :=
  (cal.originalRowsOnReports oper qpos position chart reader chargeFit).2

set_option maxRecDepth 18000 in
set_option maxHeartbeats 12000000 in
set_option cleanup.letToHave false in
private noncomputable def SignedCalendarAt.allocatedRowsOnReports : PSigma (fun goal : Prop => goal) :=
  let prepared := cal.receivedBeforeDispatchOnOriginalReports oper qpos position chart reader chargeFit
  retainOriginalRows <| fun values h reportsAt f u => (prepared values h reportsAt f u).1

/-- On the same family of report observations, the native control return prepares and
allocates its original rows before sparse emission on every issued prefix. -/
theorem SignedCalendarAt.beforeDispatchOnOriginalReports :
    (cal.allocatedRowsOnReports oper qpos position chart reader chargeFit).1 :=
  (cal.allocatedRowsOnReports oper qpos position chart reader chargeFit).2

end Diagonal

end BorderVNP
end Computability
end OAI

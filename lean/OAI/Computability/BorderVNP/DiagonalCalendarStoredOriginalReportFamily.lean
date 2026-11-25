import OAI.Computability.BorderVNP.DiagonalCalendarFundedGeometryOnOriginalReports
import OAI.Computability.BorderVNP.DiagonalCalendarSuppliedOnOriginalReports
import OAI.Computability.BorderVNP.DiagonalCalendarStoredReportFactsAtOriginalInputs
import OAI.Computability.BorderVNP.DiagonalOriginalStoredReportShape
import OAI.Computability.BorderVNP.DiagonalOriginalStoredSiteIndices
import OAI.Computability.BorderVNP.DiagonalCalendarOriginalSavedTransport

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
private def originalStoredFamilyType (coordinates issuer placement : Expr) : MetaM Expr := do
  forallBoundedTelescope (← inferType coordinates) (some 2) fun fields signature => do
    unless fields.size == 2 do throwError "the original cal field or team is missing"
    let f := fields[0]!
    let u := fields[1]!
    let history := mkProj ``Sigma 0 (mkProj ``Sigma 1 f)
    let data ← SignedCalendarAt.originalStoredSiteIndices issuer f u (mkApp placement history)
    let fixed := #[(`owner, data.owner), (`Index, data.indexType), (`index, data.index),
      (`want, data.want), (`tags, data.tags), (`rows, data.rows), (`directory, data.directory)]
    let point ← SignedCalendarAt.originalStoredReportTypeAt signature fixed
    mkForallFVars fields point

open Lean Meta Elab Term in
local elab "typeOfStoredOriginalReports%" coordinates:ident issuer:ident placement:ident : term => do
  let read (s : Ident) := elabTerm s none
  originalStoredFamilyType (← read coordinates) (← read issuer) (← read placement)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 24000000 in
set_option cleanup.letToHave false in
/-- One family of actual reported calls on the original decoded fields and teams.
The certified report carries its declaration, original row data, retained seed,
issued native call, owner table, logical reads, and original saved placement.
The source parameters of each report stay bundled with that report. -/
noncomputable def SignedCalendarAt.StoredReportsAtOriginalInputs
    (values : inputOf (sourceOnReports)) (h : inputOf ((sourceOnReports) values))
    (reports : inputOf ((sourceOnReports) values h)) : Type _ :=
  let coordinates := cal.storedReportFactsAtOriginalInputs.{0} oper qpos position chart reader chargeFit
    values h reports
  let issuer := cal.suppliedOnOriginalReports oper qpos position chart reader chargeFit values h reports
  let placement := cal.frozenOriginalPlacement_iff oper.grid qpos position chart reader chargeFit values
  typeOfStoredOriginalReports% coordinates issuer placement

end Diagonal

end BorderVNP
end Computability
end OAI

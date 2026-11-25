import OAI.Computability.BorderVNP.DiagonalCalendarOriginalReportFundingAtMarker
import OAI.Computability.BorderVNP.DiagonalOriginalCanonicalReportReceipt
import OAI.Computability.BorderVNP.DiagonalCalendarMixedOnOriginalReports
import OAI.Computability.BorderVNP.DiagonalCalendarReportGeometryOnOriginalReports
import OAI.Computability.BorderVNP.DiagonalCalendarMarkersOnOriginalReports
import OAI.Computability.BorderVNP.DiagonalOriginalFundedPlacementReturn
import OAI.Computability.BorderVNP.FiniteEvaluatorCubeStopWord

namespace OAI
namespace Computability
namespace BorderVNP

set_option autoImplicit false

/-! # Original funded sparse rows on the admitted reports -/

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

open RoutingISA.Evaluator.SignedPrep _root_.OAI.Computability.BorderVNP.Cube

open RoutingISA.FragmentRows DiagonalTallyCellReports DiagonalTallyAllocation FiniteEvaluator
open _root_.OAI.Computability.BorderVNP.Cube.Physical _root_.OAI.Computability.BorderVNP.Cube.Tally TeamContraction.JointHeader

open Lean Meta Elab Term

private def reportWitness (p : Expr) : MetaM (Expr × Expr) := do
  let some ty ← whnfUntil (← inferType p) ``Exists | throwError "expected the recorded original return"
  let args := ty.getAppArgs.push p
  return (mkAppN (mkConst ``Classical.choose ty.getAppFn.constLevels!) args,
    mkAppN (mkConst ``Classical.choose_spec ty.getAppFn.constLevels!) args)

private def actualSlot (p : Expr) : MetaM Expr := do
  let some ty ← whnfUntil (← inferType p) ``Nonempty | throwError "missing the chosen original evidence"
  return mkAppN (mkConst ``Classical.choice ty.getAppFn.constLevels!) (ty.getAppArgs.push p)

private def originalReportWindow (candidate : Expr) : MetaM Expr := do
  let (_, rest) ← reportWitness (mkProj ``And 0 candidate)
  let (_, cell) ← reportWitness rest
  let record ← actualSlot cell
  let fit ← mkProjection record `endFit
  let some less ← whnfUntil (← inferType fit) ``LT.lt | throwError "expected the original word bound"
  let some address ← whnfUntil less.getAppArgs[less.getAppNumArgs-2]! ``SignedTaskArena.Layout.endAddress |
    throwError "expected the original physical end address"
  return mkAppN (← mkConstWithLevelParams ``SignedTaskArena.Layout.cube_stop_lt_word) (address.getAppArgs.push fit)

private def fundedOriginalRows (target : Expr) : TermElabM Expr := withoutErrToSorry do
  let some family ← whnfUntil target ``SignedCalendarAt.OriginalReportEmissionRows |
    throwError "expected the original calibrated ordinal and source-value census"
  let base := family.getAppArgs
  let funding := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.fundedReadAtOriginalReportMarker) base
  let candidate := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.reportedCandidateOnOriginalReports) base
  forallBoundedTelescope target (some 5) fun issued _ => do
    let #[f, u, fit, cells, e] := issued | throwError "expected the actual field, team and emission"
    let team : Name → TermElabM Expr := fun name => do
      return mkAppN (← mkConstWithLevelParams name) (base ++ #[f, u])
    let marked ← team ``SignedCalendarAt.fundedMarkersOnOriginalReports
    let paid ← exprToSyntax (mkAppN funding #[f, u, fit, cells, e, mkProj ``And 0 marked])
    let geometry ← team ``SignedCalendarAt.reportGeometryOnOriginalReports
    let cables ← exprToSyntax (mkProj ``And 0 geometry)
    let widths ← exprToSyntax (mkProj ``And 0 (mkProj ``And 1 geometry))
    let banks ← exprToSyntax (mkProj ``And 1 (mkProj ``And 1 geometry))
    let mixed ← team ``SignedCalendarAt.mixedReportOnOriginalReports
    let (stored, returned) ← reportWitness mixed
    let memory ← exprToSyntax stored
    let here ← exprToSyntax (mkProj ``And 0 returned)
    let source ← exprToSyntax (mkProj ``And 1 (mkProj ``And 1 returned))
    let slot ← team ``SignedCalendarAt.canonicalEntryOnOriginalReports
    let placed ← exprToSyntax (← actualSlot (mkProj ``And 0 (mkProj ``And 1 (mkProj ``And 1 slot))))
    let words ← exprToSyntax (← team ``SignedCalendarAt.encodedWordsOnOriginalReports)
    let room ← exprToSyntax (← originalReportWindow (mkApp candidate f))
    let result ← elabTerm (← `(fundedOriginalReportAtPlacements% $paid
      at [$cables, $widths, $banks, $memory, $here, $source] using $placed $words $room)) none
    synthesizeSyntheticMVarsNoPostponing
    mkLambdaFVars issued (← instantiateMVars result)

set_option maxHeartbeats 18000000 in
set_option maxRecDepth 24000 in
set_option cleanup.letToHave false in
private theorem originalReportedEmissionRows
    (values : (seedBundle (tape₁) axes d₁ (order₁) position copies₁).Tables F)
    (h : Index (Fin (Module.finrank (ZMod common.p) chart.E)) (Fin (pairedTableParameters (l+1) size₁))
      (chart.pinRadius (R₁+1) r₁))
    (reports : ∀ i hist claim raw allowed,
      cal.LookupReportsAt oper qpos position chart reader chargeFit values h i hist claim raw allowed) :
    cal.OriginalReportEmissionRows oper qpos position chart reader chargeFit values h reports := by
  run_tac
    let goal ← Lean.Elab.Tactic.getMainGoal
    goal.withContext do
      goal.assign (← fundedOriginalRows (← goal.getType))
      Lean.Elab.Tactic.replaceMainGoal []

/-- The original ordinal and source-value statement on every admitted report. -/
abbrev SignedCalendarAt.OriginalReportedRowStatement : Prop := type_of% (@originalReportedEmissionRows)

/-- All original native emissions carry their scheduled cells, incoming widths,
report tails, global ordinals and values on the supplied family of raw reports. -/
theorem SignedCalendarAt.fundedEmissionRowsOnOriginalReports : SignedCalendarAt.OriginalReportedRowStatement := by
  run_tac
    (← Lean.Elab.Tactic.getMainGoal).assign (← mkConstWithLevelParams ``originalReportedEmissionRows)
    Lean.Elab.Tactic.replaceMainGoal []

end Diagonal

end BorderVNP
end Computability
end OAI

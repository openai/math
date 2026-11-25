import OAI.Computability.BorderVNP.DiagonalCalendarIssuedHostInstaller
import OAI.Computability.BorderVNP.DiagonalCalendarOwnedHostWordsType
import OAI.Computability.BorderVNP.DiagonalCalendarCanonicalReportSource
import OAI.Computability.BorderVNP.DiagonalCalendarPlannerTask
import OAI.Computability.BorderVNP.DiagonalSameReportVisits

/-! # The chosen native report on the original calendar's host cells -/

namespace OAI
namespace Computability
namespace BorderVNP

set_option autoImplicit false

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

local notation "n₁" => l+1
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
local notation "tiles" => GridHosts.tileCount axes (d₁)
local notation3 (prettyPrint := false) "order₁" => (Fintype.equivFin (Fin axes → Deck (d₁+2))).symm
local notation3 (prettyPrint := false) "geo₁" => cal.sites.choose
local notation3 (prettyPrint := false) "prog₁" => cube.signedSiteProgram paid
local notation "a₁" => FieldProcessor.freeWidth (prog₁) scales.α 32 64 (r₁) (w₁) (l+1)
local notation "extra₁" => setupWidth (w₁+1) (l+1)+(prefixCapacity (r₁) 32 64 (w₁) (l+1)+1+a₁)
local notation3 (prettyPrint := false) "tape₁" => tapeTemplate (R:=R₁) (r:=r₁) (link:=ℓ₁) (regs:=64) (w:=w₁)
  (e:=ec₁) (width:=w₁+1) (k:=l) (a:=extra₁) (prog₁) (geo₁).fits (pins₁)

variable (grid : LocatedSignedGridAt cube b header (l+1)) (qpos : 1 ≤ Q)
    (position : (Fin (Fintype.card (Cube D)) → Deck (CoverScale.initialDepth (Cube D)
      (stretch b.ρ (l+1)) (l+1)-1+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
local notation "T₁" => epochs scales.τ (l+1)
local notation "copies₁" => TeamScales.width (l+1) scales.α
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


local notation3 (prettyPrint := false) "layout₁" => cal.frozenLayout chart reader chargeFit
local notation3 (prettyPrint := false) "initial₁" => reader.startupArenaWith (n:=l+1) (reg:=64)
  (prog₁) (a₁) (ℓ₁) (layout₁).header
local notation3 (prettyPrint := false) "located₁" => cal.locatedGateTable grid qpos position (initial₁)
local notation3 (prettyPrint := false) "plan₁" => cal.seed.choose
local notation3 (prettyPrint := false) "W₁" => cal.frozenWitness
local notation3 (prettyPrint := false) "sites₁" => (Fintype.equivFin (((W₁).routedFine position).Site)).toEmbedding
local notation3 (prettyPrint := false) "edges₁" => (Fintype.equivFin (((W₁).routedFine position).Edge)).toEmbedding
local notation3 (prettyPrint := false) "ports₁" => (Fintype.equivFin (Fin (r₁) × Fin (publicWidth (tape₁)))).toEmbedding
local notation3 (prettyPrint := false) "tag₁" => ParseTable.signedLiteralCode (s:=size₁) ord
local notation3 (prettyPrint := false) "x₁" => fun _ : Unit => false

local notation3 (prettyPrint := false) "selectedSites" => cal.frozenSites grid qpos position chart reader chargeFit
local notation3 (prettyPrint := false) "table₁" => (located₁).raw.reserve ceiling₁
local notation3 (prettyPrint := false) "directory₁" => freeDirectory R₁ r₁ (initial₁).literal ℓ₁ tiles
  (GridHosts.inputBlockWidth r₁ (l+1) axes d₁) J₁ description
local notation3 (prettyPrint := false) "fresh₁" => (initial₁).next+7*(directory₁).candidates
local notation3 (prettyPrint := false) "origin₁" =>
  Allocation.dest fresh₁ cap₁ (table₁).size (located₁).outputs w₁
open BorderVNP.Cube.Physical.NativeAssignments DiagonalTallyPacketEmit

local notation3 (prettyPrint := false) "leaf(" v ")" => (plan₁).frozenLeaf tape₁ order₁ position W₁ tag₁ sites₁ edges₁ ports₁ v x₁
local notation3 (prettyPrint := false) "history(" v ")" => (packHistory (leaf(v)) (plan₁).compiled.machine.epoch T₁).Index
set_option cleanup.letToHave false
set_option maxRecDepth 18000
set_option maxHeartbeats 12000000

open RoutingISA.Evaluator.SignedPrep RoutingISA.SignedTaskArena GeometryFrameEncoding
open PackedHistoryCircuit CellMacro.Generator RoutingISA.CompactMachine
open BorderVNP.Cube.Physical.NativeAssignments Packing.RoutingOutputs
open DiagonalTallyCellReports DiagonalTallyAllocation FiniteEvaluator

local notation3 (prettyPrint := false) "planner₁" => cal.frozenPlannerTask grid qpos position chart reader chargeFit

private abbrev reportRoute {A : Type*} (_ : A → Prop) := A

private def hostReportProof {P : Prop} (proof : P) : PSigma (fun q : Prop => q) := ⟨P,proof⟩

set_option cleanup.letToHave false in
set_option maxRecDepth 18000 in
set_option maxHeartbeats 16000000 in
/-- At one real returned report, transfer its chosen local rows to the W rows of the
same route, while leaving every other team at its original owned host memory. -/
noncomputable def SignedCalendarAt.frozenHostReportAtCells
    (values : (seedBundle tape₁ axes d₁ order₁ position copies₁).Tables F) (hist : history(values)) :=
  let lift := cal.frozenLiftHostReport grid qpos position chart reader chargeFit values hist
  let src := cal.issuedReportSourceAt grid qpos position chart reader chargeFit values hist
    (fun t => ((selectedSites).publicWords t 0).val)
  let control := controlsBase origin₁ (planner₁).cube.cables (planner₁).cube.cells (dir₁).entries
    ((dir₁).teams*(dir₁).sites)
  hostReportProof <| fun (v : reportRoute src.pins) (input : Fin pins₁ → Bool) (owned : BorderVNP.Cube.TeamRows.Returns (Fin (R₁+1)) (planner₁).cube w₁)
      (u : Fin (R₁+1)) (advance : Returns SignedPrep.controls (owned.pub u) (owned.macros u) (owned.finalRegs u) (owned.output u))
      (run : Returns prepareCellReports (owned.pub u) (owned.macros u) advance.val.2.1 advance.val.2.2)
      (sections : Fin (R₁+1) → OpenSuffix.Inputs)
      (ready : ∀ t, OpenSuffix.Ready (sections t) (owned.pub t 0).val (readings (owned.output t)) w₁)
      (placed : OpenSuffix.Placement (sections u) (planner₁).cube (planner₁).before (owned.pub u 0).val
        (readings (owned.output u)))
      (axis : Fin (cube.pred+1)) {localChart : ReportLayout} {cells : List (ReportCell localChart)}
      (same : SameReportCells cells (src.cells v u))
      (seed : PreparedReportInput (owned.pub u) advance.val.2.2 cells (planner₁).after.reportCursor (dir₁).description)
      (alloc : ReportAllocation (planner₁).before (planner₁).after
        ((planner₁).cube.cellWriter ((selectedSites).publicWords u 0).val control axis) localChart cells (planner₁).after.reportCursor)
      (host : cal.OwnedHostWords grid qpos position chart reader chargeFit values hist v input owned) =>
    lift v input owned u ⟨advance,run⟩ sections ready placed (same.source_allocation alloc)
      (same.source_seed seed) rfl rfl host

end Diagonal

end BorderVNP
end Computability
end OAI

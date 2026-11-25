import OAI.Computability.BorderVNP.DiagonalCalendarSlottedWriterRoom
import OAI.Computability.BorderVNP.DiagonalCalendarPlannerTask
import OAI.Computability.BorderVNP.DiagonalCalendarSourceRoom

/-! # Bounds for the issued writer at the startup geometry address -/

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
open scoped Classical BorderVNP.Epoch.Cube

set_option maxRecDepth 7000
set_option maxHeartbeats 1900000

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
local notation "X₁" => TeamScales.exterior (ξ₁) (r₁) (l+1)

open Packing.RoutingOutputs


/-- The numeric guards for the original sparse report use the directory of
the recorded program and the address produced from its startup arena. -/
structure FundedDirectoryRoom (dir : Packing.Directory.Layout) (task : SignedTaskArena.Layout)
    (loadBase issued reportOrigin w : ℕ) : Prop where
  /-- Both literal descriptions give the same allocated geometry address. -/
  origin : issued = reportOrigin
  /-- The seven words for each directory candidate fit before the emitted geometry. -/
  reserved : loadBase + 7 * dir.candidates ≤ issued
  /-- The geometry destination fits in one native word. -/
  originFit : issued < 2^w
  /-- The cable records at that destination precede the native cube header. -/
  low : issued + 5 * task.cube.cables ≤ task.cube.header.header
  /-- At least one half-literal word is available to each private row. -/
  literalPos : 0 < dir.literal / 2
  /-- Each stored description fits inside that half-literal. -/
  shortDescription : dir.description ≤ dir.literal / 2
  /-- The planner's cell count fits in one word. -/
  wordCells : task.cube.cells ≤ 2^w
  /-- Each planner cell's stride fits in one word. -/
  wordStride : task.cube.cellStride ≤ 2^w

set_option maxHeartbeats 3200000 in
/-- Reconcile the issued geometry's startup literal with the program literal
and transfer both word bounds to the same planner used by the report. -/
theorem SignedCalendarAt.frozenFundedDirectoryRoom
    (routing : LocatedFrozenRoutingAt cube b φ q adv c charge (l+1)) :
    let issued := freeDirectory R₁ r₁ (initial₁).literal ℓ₁ tiles
      (GridHosts.inputBlockWidth r₁ (l+1) axes d₁) J₁ description
    let report := cal.frozenDirectory
    let dest := fun d : Packing.Directory.Layout => Allocation.dest ((initial₁).next+7*d.candidates)
      cap₁ ((located₁).raw.reserve ceiling₁).size (located₁).outputs w₁
    FundedDirectoryRoom report (cal.frozenPlannerTask grid qpos position chart reader chargeFit)
      (initial₁).next (dest issued) (dest report) w₁ := by
  intro issued report dest
  have spans := cal.frozenSourceRoom grid qpos position chart reader chargeFit
  have same : issued = report := spans.1
  have physical := cal.frozenSlottedWriterRoom grid qpos position chart reader chargeFit routing
  have limits := (cal.frozenArgumentPublicationRoom grid qpos position chart reader chargeFit routing).2.2
  have planner := (cal.frozenEarlyTask grid qpos position chart reader chargeFit).symm.trans
    (cal.frozenPlannerTask_eq grid qpos position chart reader chargeFit)
  have literal : 0 < report.literal / 2 :=
    (congrArg (fun d : Packing.Directory.Layout => 0 < d.literal / 2) same).mp spans.2.2.2.2.2.1
  have width : report.description ≤ report.literal / 2 :=
    (congrArg (fun d : Packing.Directory.Layout => d.description ≤ d.literal / 2) same).mp
      spans.2.2.2.2.2.2.2.2.1
  have planRoom : FundedDirectoryRoom report (cal.frozenTask grid qpos position chart reader chargeFit)
      (initial₁).next (dest report) (dest report) w₁ :=
    ⟨rfl, physical.1, physical.2.1, physical.2.2, literal, width,
      limits.2.2.2.2.1, limits.2.2.2.2.2.1⟩
  exact (congrArg₂ (fun (t : SignedTaskArena.Layout) (addr : ℕ) =>
    FundedDirectoryRoom report t (initial₁).next addr (dest report) w₁) planner
    (congrArg dest same).symm).mp planRoom

end Diagonal

end BorderVNP
end Computability
end OAI

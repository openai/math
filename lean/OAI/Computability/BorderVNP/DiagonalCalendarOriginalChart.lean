import OAI.Computability.BorderVNP.DiagonalCalendarPlannerTask
import OAI.Computability.BorderVNP.DiagonalSelectedReportRows

/-! # The original report chart on each deployed calendar team -/

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
set_option maxHeartbeats 3500000

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
local notation3 (prettyPrint := false) "task₁" => b.frozenSignedTask cube (l+1) l (size₁) header (initial₁)
  (dir₁) cap₁ ceiling₁ (located₁).outputs (w₁) (located₁).directories

local notation3 (prettyPrint := false) "selectedTask" => cal.frozenTask grid qpos position chart reader chargeFit
local notation3 (prettyPrint := false) "selectedSites" => cal.frozenSites grid qpos position chart reader chargeFit
local notation3 (prettyPrint := false) "table₁" => (located₁).raw.reserve ceiling₁
local notation3 (prettyPrint := false) "directory₁" => freeDirectory R₁ r₁ (initial₁).literal ℓ₁ tiles
  (GridHosts.inputBlockWidth r₁ (l+1) axes d₁) J₁ description
local notation3 (prettyPrint := false) "fresh₁" => (initial₁).next+7*(directory₁).candidates
local notation3 (prettyPrint := false) "origin₁" =>
  Allocation.dest fresh₁ cap₁ (table₁).size (located₁).outputs w₁
local notation3 (prettyPrint := false) "P₁" => (signedProgram (cube.cubeID paid)).program
local notation3 (prettyPrint := false) "free₁" => (selectedSites).enrichedFree prog₁ P₁ (l+1) ec₁ ℓ₁
local notation3 (prettyPrint := false) "arenaBase" =>
  Allocation.stop ((initial₁).next+7*(dir₁).candidates) cap₁ ceiling₁ (located₁).outputs w₁ w₁

open DiagonalTallyAllocation Packing.RoutingOutputs CellMacro.Generator

local notation3 (prettyPrint := false) "frame₁" => fun u : Fin (R₁+1) => ((selectedSites).publicWords u 0).val
local notation3 (prettyPrint := false) "nativeLayout" =>
  SeedPlan.signedNativeReportLayouts (S:=S) (R:=R₁) (r:=r₁) (link:=ℓ₁) (k:=l) (d:=d₁)
    (a:=extra₁) (T:=T₁) (header:=header) (cells:=Fintype.card (Cube D → Deck (EnrichedOuter.depth S (d₁+1) T₁+1)))
    prog₁ cube scales.α ξ₁ (selectedTask).p arenaBase cap₁ frame₁ (fun _ => origin₁)
local notation3 (prettyPrint := false) "control₁" => controlsBase origin₁ (selectedTask).cube.cables
  (selectedTask).cube.cells (dir₁).entries ((R₁+1)*tiles)

/-- The report directory selected for each team's original data uses the
task that was actually installed on the calendar. In particular its
control address counts all the physical cables, cells and live ports. -/
theorem SignedCalendarAt.frozenOriginalReportLayout (u : Fin (R₁+1)) :
    (nativeLayout) u = reportLayout (selectedTask).before (selectedTask).after (frame₁ u) control₁
      (selectedTask).p.parameters (selectedTask).p.siteWidth (selectedTask).p.bodyCap (selectedTask).cube.stop := by
  let chartAt (t : SignedTaskArena.Layout) := reportLayout t.before t.after (frame₁ u)
    (controlsBase origin₁ t.cube.cables t.cube.cells (dir₁).entries ((R₁+1)*tiles))
    t.p.parameters t.p.siteWidth t.p.bodyCap t.cube.stop
  have same := (cal.frozenPlannerTask_eq grid qpos position chart reader chargeFit).symm.trans
    (cal.frozenEarlyTask grid qpos position chart reader chargeFit)
  exact congrArg chartAt same

/-- On the original team's positive boot this is the actual scanner's report
chart with its saved public operand and physical control base. -/
theorem SignedCalendarAt.frozenOriginalReportLayout_on_boot (u : Fin (R₁+1)) :
    let T := selectedSites
    let P := (signedProgram (cube.cubeID paid)).program
    let G := wiringWith prog₁ P T pins₁ ℓ₁ (l+1) ec₁ (geo₁).fits
    ∀ {gen : Fragment IO} {args : Fin (R₁+1) → UnitAddresses} {pin : Fin pins₁ → Bool}
      {ext : Exterior R₁ r₁ ℓ₁ → Bool} (B : BootedPinStart gen G T.publicWords T.registers args pin ext u),
      (nativeLayout) u = reportLayout (selectedTask).before (selectedTask).after (B.start.pub 0).val control₁
        (selectedTask).p.parameters (selectedTask).p.siteWidth (selectedTask).p.bodyCap (selectedTask).cube.stop := by
  intro T P G gen args pin ext B
  exact cal.frozenOriginalReportLayout grid qpos position chart reader chargeFit u

local notation3 (prettyPrint := false) "planner" =>
  cal.frozenPlannerTask grid qpos position chart reader chargeFit

/-- The same native chart stated directly for the task that consumes the
original funded emission, with its planner control pointer. -/
theorem SignedCalendarAt.frozenOriginalPlannerLayout_on_boot (u : Fin (R₁+1)) :
    let T := selectedSites
    let P := (signedProgram (cube.cubeID paid)).program
    let G := wiringWith prog₁ P T pins₁ ℓ₁ (l+1) ec₁ (geo₁).fits
    ∀ {gen : Fragment IO} {args : Fin (R₁+1) → UnitAddresses} {pin : Fin pins₁ → Bool}
      {ext : Exterior R₁ r₁ ℓ₁ → Bool} (B : BootedPinStart gen G T.publicWords T.registers args pin ext u),
      (nativeLayout) u = reportLayout (planner).before (planner).after (B.start.pub 0).val (controlsBase origin₁ (planner).cube.cables (planner).cube.cells (dir₁).entries ((R₁+1)*tiles))
        (planner).p.parameters (planner).p.siteWidth (planner).p.bodyCap (planner).cube.stop := by
  intro T P G gen args pin ext B
  let chartAt (t : SignedTaskArena.Layout) := reportLayout t.before t.after (B.start.pub 0).val
    (controlsBase origin₁ t.cube.cables t.cube.cells (dir₁).entries ((R₁+1)*tiles))
    t.p.parameters t.p.siteWidth t.p.bodyCap t.cube.stop
  have same := (cal.frozenEarlyTask grid qpos position chart reader chargeFit).symm.trans
    (cal.frozenPlannerTask_eq grid qpos position chart reader chargeFit)
  exact (cal.frozenOriginalReportLayout_on_boot grid qpos position chart reader chargeFit u B).trans
    (congrArg chartAt same)

end Diagonal

end BorderVNP
end Computability
end OAI

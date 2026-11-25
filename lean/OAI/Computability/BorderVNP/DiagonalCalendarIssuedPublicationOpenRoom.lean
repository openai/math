import OAI.Computability.BorderVNP.DiagonalCalendarIssuedPlacement
import OAI.Computability.BorderVNP.DiagonalCalendarPlannerTask
import OAI.Computability.BorderVNP.DiagonalCalendarReportOpenRoom

/-! # Opening a report at the destination of the issued geometry table -/

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
local notation "tiles" => GridHosts.tileCount axes (d₁)
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

open Packing.RoutingOutputs

local notation3 (prettyPrint := false) "planner₁" => cal.frozenPlannerTask grid qpos position chart reader chargeFit
local notation "nativeCells" => Fintype.card (Cube D → Deck (EnrichedOuter.depth S (d₁+1) T₁+1))
local notation "liveCount" => (R₁+1)*tiles
local notation3 (prettyPrint := false) "issuedDir" => freeDirectory R₁ r₁ (initial₁).literal ℓ₁ tiles
  (GridHosts.inputBlockWidth r₁ (l+1) axes d₁) J₁ description
local notation3 (prettyPrint := false) "sourceOrigin" => Allocation.dest ((initial₁).next+7*(dir₁).candidates)
  cap₁ ceiling₁ (located₁).outputs w₁
local notation3 (prettyPrint := false) "issuedOrigin" => Allocation.dest ((initial₁).next+7*(issuedDir).candidates)
  cap₁ ((located₁).raw.reserve ceiling₁).size (located₁).outputs w₁

private abbrev reportRoom (ar : SignedTaskArena.Layout) (base origin entries live cells w : ℕ) : Prop :=
  let table := bases origin ar.cube.cables ar.cube.cells entries
  ar.OpenRoom base table.ends (controlsBase origin ar.cube.cables ar.cube.cells entries live)
    table.livePairs live entries (2^BottomReports.BundleSort.markedDepth cells entries) w

private theorem reportRoom_of_coordinates {ar : SignedTaskArena.Layout}
    {base reserved issued entries live cells w : ℕ} (location : issued=reserved)
    (count : cells=ar.cube.cells) (room : reportRoom ar base reserved entries live cells w) :
    reportRoom ar base issued entries live ar.cube.cells w := by
  rw [location,←count]
  exact room

/-- Use the measured space of an arbitrary returned processor at the address of
the issued directory and table, with the sort depth of the planner's own cell array. -/
theorem SignedCalendarAt.openRoomAtIssuedOrigin {base : ℕ}
    (room : (planner₁).OpenRoom base
      (bases sourceOrigin (planner₁).cube.cables (planner₁).cube.cells J₁).ends
      (controlsBase sourceOrigin (planner₁).cube.cables (planner₁).cube.cells J₁ liveCount)
      (bases sourceOrigin (planner₁).cube.cables (planner₁).cube.cells J₁).livePairs
      liveCount J₁ (2^BottomReports.BundleSort.markedDepth nativeCells J₁) w₁) :
    (planner₁).OpenRoom base
      (bases issuedOrigin (planner₁).cube.cables (planner₁).cube.cells (dir₁).entries).ends
      (controlsBase issuedOrigin (planner₁).cube.cables (planner₁).cube.cells (dir₁).entries
        ((dir₁).teams*(dir₁).sites))
      (bases issuedOrigin (planner₁).cube.cables (planner₁).cube.cells (dir₁).entries).livePairs
      ((dir₁).teams*(dir₁).sites) (dir₁).entries
      (2^BottomReports.BundleSort.markedDepth (planner₁).cube.cells (dir₁).entries) w₁ := by
  have destination := (cal.frozenIssuedPlacement grid qpos position chart reader chargeFit).2.2.1
  have cells := congrArg (fun t : SignedTaskArena.Layout => t.cube.cells)
    (cal.frozenPlannerTask_eq grid qpos position chart reader chargeFit)
  exact reportRoom_of_coordinates (ar:=planner₁) (base:=base) (entries:=J₁) (live:=liveCount)
    (cells:=nativeCells) (w:=w₁) destination cells room

end Diagonal

end BorderVNP
end Computability
end OAI

import OAI.Computability.BorderVNP.DiagonalCalendarFundedReportAddresses
import OAI.Computability.BorderVNP.DiagonalProducedRoster

/-! # The original planner addresses of the supported funded roster -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.ScheduleClock

open VPVNP.BurstRAM

/-- The same placed cells and sparse builder input at three specified
physical addresses: the row ends, control table, and live pairs. -/
abbrev RosterAtReportAddresses {w : ℕ} (a : SignedTaskArena.Layout) (team frame ports : ℕ)
    (pub : Arg → Word w) (mem : Memory w) (raw : ℕ → ℕ) (addr : ℕ × ℕ × ℕ) : Prop :=
  ∃ (Orig : Type) (placed : ℕ → CellPacket.Placed Orig) (geometry : ℕ → ℕ)
    (extras : ℕ → List CellSparse.Record) (input : SparseCallInput pub mem),
    ProducedRoster a (a.controlRows team frame addr.1 addr.2.1 addr.2.2 ports) raw placed geometry extras input

end RoutingISA.Evaluator.ScheduleClock

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
local notation "R₁" => b.physical.teamsPred (l+1)
local notation "w₁" => b.physical.word (l+1)
local notation "ξ₁" => (scales.τ:ℝ)/5
local notation "ℓ₁" => TeamScales.link (ξ₁) (R₁+1) (l+1)
local notation "d₁" => CoverScale.initialDepth (Cube D) (r₁) (l+1)-1
local notation "axes" => Fintype.card (Cube D)
local notation "tiles" => GridHosts.tileCount axes (d₁)
local notation3 (prettyPrint := false) "prog₁" => cube.signedSiteProgram paid
local notation "a₁" => FieldProcessor.freeWidth (prog₁) scales.α 32 64 (r₁) (w₁) (l+1)

variable (grid : LocatedSignedGridAt cube b header (l+1)) (qpos : 1 ≤ Q)
    (position : (Fin (Fintype.card (Cube D)) → Deck (CoverScale.initialDepth (Cube D)
      (stretch b.ρ (l+1)) (l+1)-1+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
local notation "T₁" => epochs scales.τ (l+1)
local notation "J₁" => (fan S)^T₁*tiles
local notation "description" => seedDescriptionWidth (l+1) (r₁) axes (d₁) (header*logWidth (r₁) (l+1))
  (BottomGridBank.bodyBudget (seedBoxCapacity (l+1) (r₁) axes (d₁) (Fintype.card (Direction axes))))
local notation "cap₁" => SeedPlan.profileReserve (r₁) (l+1)
local notation "ceiling₁" => geometryGateCeiling (8*(11920000+1500000+16008100*coeff+37)) (4*(E+2)) (r₁) (l+1)

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

local notation3 (prettyPrint := false) "selectedTask" => cal.frozenTask grid qpos position chart reader chargeFit
local notation3 (prettyPrint := false) "table₁" => (located₁).raw.reserve ceiling₁
local notation3 (prettyPrint := false) "directory₁" => freeDirectory R₁ r₁ (initial₁).literal ℓ₁ tiles
  (GridHosts.inputBlockWidth r₁ (l+1) axes d₁) J₁ description
local notation3 (prettyPrint := false) "fresh₁" => (initial₁).next+7*(directory₁).candidates
open BorderVNP.Cube.Physical.NativeAssignments DiagonalTallyPacketEmit


local notation3 (prettyPrint := false) "planner" => cal.frozenPlannerTask grid qpos position chart reader chargeFit
local notation3 (prettyPrint := false) "origin₁" =>
  Allocation.dest fresh₁ cap₁ (table₁).size (located₁).outputs w₁
local notation3 (prettyPrint := false) "cells₁" =>
  CoverScale.sites (Cube D) (EnrichedOuter.depth S (d₁+1) T₁)
local notation3 (prettyPrint := false) "cables₁" =>
  (boundaryShape S (d₁+1) T₁).edges+4*(R₁+1)*tiles
local notation3 (prettyPrint := false) "live₁" => (R₁+1)*tiles



open RoutingISA.Evaluator.ScheduleClock TeamContraction.JointHeader
set_option maxRecDepth 16000
set_option maxHeartbeats 10500000
set_option cleanup.letToHave false


/-- Read the original returned roster with the planner's row ends, control
address and live-pairs address. The literal geometry has equal coordinates. -/
theorem SignedCalendarAt.fundedRosterAtPlanner {w : ℕ} {pub : Arg → Word w} {mem : Memory w}
    {team frame : ℕ} {raw : ℕ → ℕ} :
    let coordinates (dims : ℕ × ℕ) :=
      let table := RoutingOutputs.bases origin₁ dims.2 dims.1 (directory₁).entries
      (table.ends,RoutingOutputs.controlsBase origin₁ dims.2 dims.1 (directory₁).entries live₁,table.livePairs)
    let native := ((planner).cube.cells,(planner).cube.cables)
    let literal := (cells₁,cables₁)
    ScheduleClock.RosterAtReportAddresses planner team frame live₁ pub mem raw (coordinates literal) →
      ScheduleClock.RosterAtReportAddresses planner team frame live₁ pub mem raw (coordinates native) := by
  intro coordinates native literal found
  have planned := cal.frozenPlannerTask_eq grid qpos position chart reader chargeFit
  have counts : native=literal :=
    congrArg (fun a : SignedTaskArena.Layout => (a.cube.cells,a.cube.cables)) planned.symm
  exact (congrArg (fun dims => ScheduleClock.RosterAtReportAddresses planner team frame live₁ pub mem raw
    (coordinates dims)) counts).mpr found

end Diagonal

end BorderVNP
end Computability
end OAI

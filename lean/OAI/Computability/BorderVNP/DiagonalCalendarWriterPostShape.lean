import OAI.Computability.BorderVNP.DiagonalCalendarSourceRoom
import OAI.Computability.BorderVNP.DiagonalCalendarEarlyParameters

/-! # Header and control coordinates of the calendar’s physical post request -/

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

set_option maxRecDepth 11000
set_option maxHeartbeats 4300000

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
open RoutingOutputs
local notation "symbols₁" => BorderVNP.Cube.alphabet scales.α (l+1)
local notation "traffic₁" => (((R₁+1)*exterior (ξ₁) (r₁) (l+1)) : ℕ)
local notation3 (prettyPrint := false) "headerCap₁" => BorderVNP.Cube.Physical.declarationCap cube.pred symbols₁
  (BorderVNP.Cube.Physical.blocksFor traffic₁ (cube.h*cube.b) (symbols₁^(cube.pred+1))) cube.b cube.h cube.width
local notation3 (prettyPrint := false) "cells₁" => CoverScale.sites (Cube D) (EnrichedOuter.depth S ((d₁)+1) T₁)
local notation3 (prettyPrint := false) "cables₁" => (boundaryShape S ((d₁)+1) T₁).edges+4*(R₁+1)*tiles
local notation "live₁" => (R₁+1)*tiles
local notation3 (prettyPrint := false) "dest₁" => Allocation.dest ((initial₁).next+7*(dir₁).candidates)
  cap₁ ceiling₁ (located₁).outputs w₁
local notation3 (prettyPrint := false) "ctl₁" => controlsBase dest₁ cables₁ cells₁ J₁ live₁
local notation3 (prettyPrint := false) "selectedTask" => cal.frozenTask grid qpos position chart reader chargeFit
local notation3 (prettyPrint := false) "directory₁" => freeDirectory R₁ r₁ (initial₁).literal ℓ₁ tiles
  (GridHosts.inputBlockWidth r₁ (l+1) axes d₁) J₁ description
local notation3 (prettyPrint := false) "physicalDest" => Allocation.dest ((initial₁).next+7*(directory₁).candidates)
  cap₁ ((located₁).raw.reserve ceiling₁).size (located₁).outputs w₁
local notation3 (prettyPrint := false) "physicalCtl" => controlsBase physicalDest
  (selectedTask).cube.cables (selectedTask).cube.cells (directory₁).entries ((directory₁).teams*(directory₁).sites)

/-- The directory and controls of the booted writer agree with the geometric finish
layout. The same selected cube supplies the axis count and declaration capacity. -/
theorem SignedCalendarAt.frozenWriterPostShape :
    directory₁=dir₁ ∧ physicalCtl=ctl₁ ∧ headerCap₁=(selectedTask).cube.header.cap ∧ (selectedTask).cube.n=cube.pred := by
  let task := selectedTask
  have dirEq : directory₁=dir₁ := (cal.frozenSourceRoom grid qpos position chart reader chargeFit).1
  have cells : task.cube.cells=cells₁ :=
    (congrArg (fun t : SignedTaskArena.Layout => t.cube.cells) (cal.frozenEarlyTask grid qpos position chart reader chargeFit)).symm
  have cables : task.cube.cables=cables₁ :=
    (congrArg (fun t : SignedTaskArena.Layout => t.cube.cables) (cal.frozenEarlyTask grid qpos position chart reader chargeFit)).symm
  refine ⟨dirEq,?_,rfl,rfl⟩
  change controlsBase physicalDest task.cube.cables task.cube.cells (directory₁).entries ((directory₁).teams*(directory₁).sites)=_
  rw [dirEq,cables,cells,(located₁).raw.reserve_size ceiling₁ (located₁).raw_bound]
  rfl

end Diagonal

end BorderVNP
end Computability
end OAI

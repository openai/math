import OAI.Computability.BorderVNP.DiagonalCalendarReportInventory
import OAI.Computability.BorderVNP.DiagonalCalendarFeasiblePost
import OAI.Computability.BorderVNP.DiagonalCalendarIssuedPlacement
import OAI.Computability.BorderVNP.DiagonalCalendarTaskRoom
import OAI.Computability.BorderVNP.DiagonalCalendarBootChecks
import OAI.Computability.BorderVNP.DiagonalCalendarFinishSortShape
import OAI.Computability.BorderVNP.DiagonalCalendarPostRate
import OAI.Computability.BorderVNP.DiagonalDeployedFeasiblePost

/-! # Reader finish addresses on the actual issued report control rectangle -/

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
set_option maxHeartbeats 4300000

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

local notation "par₁" => pairedTableParameters (l+1) (size₁)
local notation "cubeEntries" => _root_.OAI.Computability.BorderVNP.Cube.TableEntry cube.pred cube.b cube.h cube.copies cube.width
local notation "gadgets" => Fintype.card (paid.Entry ⊕ cubeEntries)
local notation "query₁" => Fintype.card (Board.Physical (par₁) (budget₁+6) w₁ (paid.Entry ⊕ cubeEntries))
local notation "guess₁" => Fintype.card (Guess (Fin (par₁)) reader.gridRank (Nat.clog 2 common.p+1) (Nat.clog 2 common.p))


open CellPacketGeometry TerminalCells RoutingOutputs RoutingISA.SignedTaskArena
open TeamContraction.JointHeader RoutingISA.Evaluator.ScheduleClock
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
local notation3 (prettyPrint := false) "start₁" => Retained.packetBase dest₁ cables₁ cells₁ J₁ live₁ 37
local notation "digits₁" => Nat.clog 2 (r₁*(2*l+1)+1)
local notation "public₁" => ⌈publicWork (cube.pred+1) scales.α (r₁) (l+1) (R₁+1)⌉₊
local notation "local₁" => ⌈localWork (cube.pred+1) (E+2) scales.α (ξ₁) (r₁) (l+1) (R₁+1)⌉₊

local notation3 (prettyPrint := false) "issued" => freeDirectory R₁ r₁ (initial₁).literal ℓ₁ tiles
  (GridHosts.inputBlockWidth r₁ (l+1) axes d₁) J₁ description
local notation3 (prettyPrint := false) "actualTask" => cal.frozenTask grid qpos position chart reader chargeFit
local notation3 (prettyPrint := false) "actualOrigin" => Allocation.dest ((initial₁).next+7*(issued).candidates)
  cap₁ ((located₁).raw.reserve ceiling₁).size (located₁).outputs w₁

set_option cleanup.letToHave false in
/-- The observed header dimensions and the actual source directory point at
the same reader and sparse-call placement after the last registered report. -/
theorem SignedCalendarAt.frozenIssuedFinishAddresses (rates : CalendarPostRateAt cube b φ q adv c charge (l+1)) :
    let task := actualTask
    let ctl := controlsBase actualOrigin task.cube.cables task.cube.cells (issued).entries ((issued).teams*(issued).sites)
    task.FinishAddresses initial₁ ctl task.cube.header.profile task.cube.n task.cube.header.d task.cube.header.cap
      w₁ w₁ query₁ guess₁ reader.gates := by
  intro task ctl
  have nc : task.cube.cells=cells₁ := by
    change (actualTask).cube.cells=_
    rw [cal.frozenTask_eq_selected grid qpos position chart reader chargeFit]
    rfl
  have ne : task.cube.cables=cables₁ := by
    change (actualTask).cube.cables=_
    rw [cal.frozenTask_eq_selected grid qpos position chart reader chargeFit]
    change (boundary S (d₁+1) T₁).edges+4*((R₁+1)*CoverScale.sites (Cube D) (d₁+1))=_
    rw [grid.tiles_eq,Nat.mul_assoc]
    rfl
  have origin := (cal.frozenIssuedPlacement grid qpos position chart reader chargeFit).2.2.1
  have same : ctl=ctl₁ := by
    dsimp only [ctl]
    rw [origin,nc,ne]
    rfl
  have dims : task.cube.header.profile=cap₁ ∧ task.cube.n=cube.pred ∧ task.cube.header.d=symbols₁ ∧
      task.cube.header.cap=headerCap₁ := by
    change (actualTask).cube.header.profile=cap₁ ∧ (actualTask).cube.n=cube.pred ∧
      (actualTask).cube.header.d=symbols₁ ∧ (actualTask).cube.header.cap=headerCap₁
    rw [cal.frozenTask_eq_selected grid qpos position chart reader chargeFit]
    exact ⟨rfl,rfl,rfl,rfl⟩
  rw [same,dims.1,dims.2.1,dims.2.2.1,dims.2.2.2]
  exact (cal.frozenDeployedFeasiblePost grid qpos position chart reader chargeFit rates).addresses

end Diagonal

end BorderVNP
end Computability
end OAI

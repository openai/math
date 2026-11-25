import OAI.Computability.BorderVNP.DiagonalCalendarTaskRoom
import OAI.Computability.BorderVNP.DiagonalCalendarBootChecks
import OAI.Computability.BorderVNP.DiagonalCalendarFinishSortShape
import OAI.Computability.BorderVNP.DiagonalCalendarPostRate
import OAI.Computability.BorderVNP.DiagonalDeployedFeasiblePost

/-! # The scanner address and finish budgets of the installed calendar task -/

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
local notation "marked₁" => BottomReports.BundleSort.markedDepth cells₁ J₁
local notation "public₁" => ⌈publicWork (cube.pred+1) scales.α (r₁) (l+1) (R₁+1)⌉₊
local notation "local₁" => ⌈localWork (cube.pred+1) (E+2) scales.α (ξ₁) (r₁) (l+1) (R₁+1)⌉₊

private theorem placed_ranges (task : SignedTaskArena.Layout) (a : StartupArena)
    (candidates reserve gates originals live p d depth chunks field w outputs : ℕ)
    (shape : outputs=signedGridOutputCount task.cube.cables task.cube.cells originals live 37 (Total p d)+(2^depth+2^depth)) :
    let fresh := a.next+7*candidates
    let dest := Allocation.dest fresh reserve gates outputs field
    let ctl := controlsBase dest task.cube.cables task.cube.cells originals live
    let start := Retained.packetBase dest task.cube.cables task.cube.cells originals live 37
    let dirs := GeometryDirectories.published start p d (task.cube.cells+1) chunks ctl (Total p d) depth
    task.cube.header.header=Allocation.stop fresh reserve gates outputs field w →
    task.p.sorted=dirs.sorted → task.p.padded=dirs.padded → task.cube.cells≤task.p.report.cells →
    task.SparsePlacement a.frame ctl ∧ task.p.sorted+task.p.padded≤task.cube.header.packetBase ∧
      ctl+37≤task.cube.header.packetBase ∧ a.next≤ctl ∧ a.next≤task.p.sorted := by
  subst outputs
  intro fresh dest ctl start dirs base sorted padded cells
  obtain ⟨location,safe,space⟩ := Retained.signed_finish_directories task a candidates reserve gates originals
    live p d depth field w chunks base sorted padded cells
  have startBelow : a.next+7*candidates≤dest := by dsimp only [dest,fresh,Allocation.dest,Allocation.temp]; omega
  have ctlAbove : a.next≤ctl := ((Nat.le_add_right ..).trans startBelow).trans (by dsimp only [ctl,controlsBase,bases]; omega)
  have sortedAbove : ctl≤task.p.sorted := by
    rw [sorted]
    change ctl≤(ctl+37)+(2^p+2^p)
    exact (Nat.le_add_right ..).trans (Nat.le_add_right ..)
  exact ⟨location,safe,space,ctlAbove,ctlAbove.trans sortedAbove⟩

/-- The physical calendar's own sort arrays, pinned reader and declared cube
share these finish bounds at the chosen length. The two batch inequalities
were measured before the field chart or execution was selected. -/
theorem SignedCalendarAt.frozenDeployedFeasiblePostOfShape
    (rates : CalendarPostRateAt cube b φ q adv c charge (l+1))
    {wp wd chunks : ℕ}
    (arity : (located₁).outputs=signedGridOutputCount cables₁ cells₁ J₁ live₁ 37 (Total wp wd)+(2^marked₁+2^marked₁))
    (directories : (located₁).directories=GeometryDirectories.published start₁ wp wd (cells₁+1) chunks
      ctl₁ (Total wp wd) marked₁) (total : Total wp wd ≤ (located₁).outputs) :
    let task := cal.frozenTask grid qpos position chart reader chargeFit
    task.DeployedFeasiblePost initial₁ dir₁ ctl₁ cap₁ cube.pred symbols₁ headerCap₁ w₁ query₁ guess₁ reader.gates
      pins₁ r₁ wp wd digits₁ (exterior ξ₁ r₁ (l+1)) public₁ local₁ reader.charge (R₁+1) par₁ gadgets := by
  intro task
  have nc : task.cube.cells=cells₁ := by
    change CoverScale.sites (Cube D) (EnrichedOuter.depth S _ T₁)=_
    rw [grid.depth_eq]
  have ne : task.cube.cables=cables₁ := by
    change (boundary S _ T₁).edges+4*((R₁+1)*CoverScale.sites (Cube D) _)=_
    rw [grid.depth_eq,grid.tiles_eq,Nat.mul_assoc]
    rfl
  have geometry := placed_ranges task initial₁ (dir₁).candidates cap₁ ceiling₁ J₁ live₁ wp wd marked₁ chunks
    w₁ w₁ (located₁).outputs (by rw [ne,nc]; exact arity)
  dsimp only at geometry
  rw [ne,nc] at geometry
  have sorted : task.p.sorted=(located₁).directories.sorted := rfl
  have padded : task.p.padded=(located₁).directories.padded := rfl
  obtain ⟨place,sortBound,ctlBound,above,protectedSort⟩ := geometry rfl
    (sorted.trans (congrArg GeometryDirectories.sorted directories))
    (padded.trans (congrArg GeometryDirectories.padded directories)) (nc ▸ (le_rfl : task.cube.cells≤task.p.report.cells))
  have saved := cal.frozenTask_room grid qpos position chart reader chargeFit
  have endFit : task.endAddress w₁ query₁ guess₁ reader.gates<2^w₁ := saved.2.1
  have fits := task.finish_word_room endFit
  have hdr : (initial₁).header=PositiveFields.width cap₁ cube.pred symbols₁ headerCap₁ task.cube.teams task.dim w₁ :=
    (cal.frozenLayout_fields chart reader chargeFit).1
  have addrFit : task.FinishAddresses initial₁ ctl₁ cap₁ cube.pred symbols₁ headerCap₁ w₁ w₁ query₁ guess₁ reader.gates :=
    ⟨endFit,saved.2.2.1,hdr,le_rfl,fits.1,fits.2.1,fits.2.2.1,place,sortBound,ctlBound,rfl,rfl,rfl,
      fun z => (Fintype.equivFin (paid.Entry ⊕ cubeEntries) (.inr z)).isLt,above,protectedSort⟩
  obtain ⟨slots,rectangle⟩ := rates l rfl chart reader chargeFit
  have ξsmall : (ξ₁) ≤ 1 := by linarith [scales.tau_small,scales.alpha_small]
  have budgets := post_window_capacities (a:=cube.pred+1) (D:=E+2) (α:=scales.α) (ξ:=ξ₁)
    (Nat.succ_pos l) (stretch_one b.ρ (l+1)) (Nat.succ_pos (R₁)) ξsmall addrFit.wordPos addrFit.wordPos
    total (located₁).packet_bound slots
  have copied : reader.packetBitCount≤r₁ := (cal.frozenBootBounds grid qpos position chart reader chargeFit).2.1
  have count : reader.packetBitCount=w₁*(6+3*reader.gates+query₁+81)+pins₁ := rfl
  have arena := reader.frozenTask_startupArena geo₁ ℓ₁ (layout₁).header
  have literalPositive : 1≤literal scales.α (l+1) := Nat.le_floor (by
    simpa using Real.one_le_rpow (by exact_mod_cast Nat.succ_pos l : 1≤((l+1:ℕ):ℝ))
      (show 0≤1-(scales.α:ℝ)/3 by linarith [scales.alpha_small]))
  refine ⟨addrFit,⟨slots,rectangle,budgets.1,budgets.2.1,budgets.2.2⟩,rfl,rfl,rfl,rfl,cube.block_pos,
    Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (by positivity) _),?_,?_,?_,saved.2.2.2.2.1⟩
  · intro pp lp
    exact Nat.add_le_add_right ((dir₁).directory_length_le pp lp) _
  · change (6+3*reader.gates+query₁)*w₁ ≤ reader.packetBitCount
    rw [count,Nat.mul_comm (6+3*reader.gates+query₁)]
    exact (Nat.mul_le_mul_left _ (Nat.le_add_right _ 81)).trans (Nat.le_add_right _ _)
  · have extent : (initial₁).count = r₁*literal scales.α (l+1) := congrArg StartupArena.count arena
    exact (((Nat.le_add_left ..).trans (count ▸ copied)).trans (Nat.le_mul_of_pos_right _ literalPositive)).trans_eq extent.symm

/-- On the deployed calendar the calibrated finish uses the actual private
scanner, the two installed sort depths and the common pin banks. -/
theorem SignedCalendarAt.frozenDeployedFeasiblePost (rates : CalendarPostRateAt cube b φ q adv c charge (l+1)) :
    let dims := cal.frozenPacketSortShape grid position
    let task := cal.frozenTask grid qpos position chart reader chargeFit
    task.DeployedFeasiblePost initial₁ dir₁ ctl₁ cap₁ cube.pred symbols₁ headerCap₁ w₁ query₁ guess₁ reader.gates
      pins₁ r₁ dims.1 dims.2.1 digits₁ (exterior ξ₁ r₁ (l+1)) public₁ local₁ reader.charge (R₁+1) par₁ gadgets := by
  intro dims task
  obtain ⟨arity,placed,total⟩ := cal.locatedGateTable_finishSortShape grid qpos position initial₁
  exact cal.frozenDeployedFeasiblePostOfShape grid qpos position chart reader chargeFit rates arity placed total

end Diagonal

end BorderVNP
end Computability
end OAI

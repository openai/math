import OAI.Computability.BorderVNP.DiagonalCalendarFrozenRouting
import OAI.Computability.BorderVNP.DiagonalCalendarControlWords
import OAI.Computability.BorderVNP.DiagonalCalendarSourceRoom

/-! # Address and size bounds for publication on the deployed signed calendar -/

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


private theorem publicationFloor (origin cables cells entries ports : ℕ) :
    origin ≤ controlsBase origin cables cells entries ports := by
  dsimp only [controlsBase,bases]
  omega

private theorem publicationStop {stop extra w : ℕ} (fit : 1000000*(stop+extra)+2*stop<2^w) : stop<2^w := by omega

private theorem publicationWord {ctl hdr w : ℕ} (below : ctl+37 ≤ hdr) (fit : hdr<2^w) : ctl+8<2^w := by omega

/-- The actual signed evaluator can represent the exterior budget, the
whole cube, its private directory and all control addresses on this same
calendar. These bounds are chosen before either free pin or header. -/
theorem SignedCalendarAt.frozenPublicationRoom
    (routing : LocatedFrozenRoutingAt cube b φ q adv c charge (l+1)) :
    let ar := (cal.frozenTask grid qpos position chart reader chargeFit).cube
    let dir := cal.frozenDirectory
    let tab := located₁
    let fresh := (initial₁).next+7*dir.candidates
    let dest := Allocation.dest fresh cap₁ (tab.raw.reserve ceiling₁).size tab.outputs w₁
    let ctl := controlsBase dest ar.cables ar.cells dir.entries (dir.teams*dir.sites)
    X₁<2^w₁ ∧ ar.stop<2^w₁ ∧ ar.cells≤2^w₁ ∧ fresh≤dest ∧ fresh≤ar.header.header ∧
      ctl+8<2^w₁ ∧ r₁≤tiles ∧ 0<r₁ ∧ 0<dir.literal/2 ∧
      dir.entries*dir.description≤dir.teams*dir.processors*(dir.literal/2) ∧
      dir.description≤dir.literal ∧ ar.teams=R₁+1 := by
  intro ar dir tab fresh dest ctl
  obtain ⟨guard,_,controls,_,privateWords⟩ := cal.locatedGateTable_routing grid qpos position chart reader chargeFit routing
  have native := cal.frozenSourceRoom grid qpos position chart reader chargeFit
  have headerFit := (cal.frozenControlFormats grid qpos position chart reader chargeFit).2.2.1
  have scaled := guard.scaled
  have xFit : X₁ < 2^w₁ := by
    apply lt_of_le_of_lt _ scaled
    exact (Nat.le_mul_of_pos_left _ (by decide : 0<1000000)).trans (Nat.le_mul_of_pos_right _ (by exact Nat.succ_pos _))
  have stop : ar.stop < 2^w₁ := publicationStop guard.rawSpace
  have stride : 0 < ar.cellStride := Nat.succ_pos _
  have cellFit : ar.cells ≤ 2^w₁ := ((Nat.le_mul_of_pos_right _ stride).trans (Nat.le_add_left ..)).trans stop.le
  have start : fresh ≤ dest := by dsimp only [dest,Allocation.dest,Allocation.temp]; omega
  have ceiling : ctl + 37 ≤ ar.header.header := controls
  have floor := publicationFloor dest ar.cables ar.cells dir.entries (dir.teams*dir.sites)
  have low : fresh ≤ ar.header.header := start.trans (floor.trans ((Nat.le_add_right ctl 37).trans ceiling))
  have budget : ctl+8<2^w₁ := publicationWord ceiling headerFit
  obtain ⟨same,_,_,_,_,halfPos,_,_,half,_,_⟩ := native
  rw [same] at halfPos half
  exact ⟨xFit,stop,cellFit,start,low,budget,grid.processors_le_tiles,stretch_one b.ρ (l+1),
    halfPos,privateWords,half.trans (Nat.div_le_self ..),rfl⟩

end Diagonal

end BorderVNP
end Computability
end OAI

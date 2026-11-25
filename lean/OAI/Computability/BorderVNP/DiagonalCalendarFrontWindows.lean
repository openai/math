import OAI.Computability.BorderVNP.DiagonalCalendarFrozenRouting
import OAI.Computability.BorderVNP.DiagonalLocatedTableFront

/-! # The true route windows of the calendar’s selected deployed table -/

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
local notation3 (prettyPrint := false) "task₁" => b.frozenSignedTask cube (l+1) l (size₁) header (initial₁)
  (dir₁) cap₁ ceiling₁ (located₁).outputs (w₁) (located₁).directories

local notation "X₁" => TeamScales.exterior (ξ₁) (r₁) (l+1)
local notation3 (prettyPrint := false) "orig₁" => Allocation.dest ((initial₁).next+7*(dir₁).candidates) cap₁
  ((located₁).raw.reserve ceiling₁).size (located₁).outputs (w₁)

open Packing.RoutingOutputs

open RoutingISA.Evaluator.ScheduleClock

attribute [local irreducible] Nat.clog

private theorem front_sizes {cables cells originals live controls packet tail total : ℕ}
    (count : total=TerminalCells.signedGridOutputCount cables cells originals live controls packet+tail) :
    cells≤total ∧ originals≤total := by unfold TerminalCells.signedGridOutputCount at count; omega

set_option maxHeartbeats 3800000 in
/-- The full located gate packet and the four words of the published demand
directory pay both route windows on the selected calendar task. The address
scale, header, and both projected banks precede the choice of any rows. -/
theorem SignedCalendarAt.frozenSites_front_windows (phaseDegree setupWork emitted vertices : ℕ)
    (front : LocatedTableFrontAt cube b phaseDegree setupWork emitted vertices (l+1))
    (routing : LocatedFrozenRoutingAt cube b φ q adv c charge (l+1)) :
    let ar := (task₁).cube
    let dir := dir₁
    let t := located₁
    let initial := initial₁
    let windows := scales.signedWindows phaseDegree (512*((cube.pred+1)+
      _root_.OAI.Computability.BorderVNP.Cube.Tally.selectorWidth cube.pred cube.copies cube.h+1)) setupWork emitted vertices (l+1) r₁
    ∀ pp lp, ∀ axis : ℕ, ∀ after : ℕ → ℕ,
      let rows := dir.directory pp lp
      let tab := ar.table initial.frame (rows.length+ar.header.d.choose 2)
      let labels := _root_.OAI.Computability.BorderVNP.Cube.LabelIndex.layout initial.frame after
      labels.cells=ar.cells → labels.cableCount=ar.cables → labels.deliveryCount=rows.length → labels.labels=ar.alphabet →
      2048*(X₁+(R₁+1+1)^3+tab.count+r₁+1)≤windows.core ∧
        GeometryAdviceRate.ticks (t.raw.reserve ceiling₁).size cap₁ t.outputs w₁ w₁+
          beforeDirectory (R₁+1) dir.sites dir.entries+
          rawScheduleTicks ar initial.frame initial.broadcastBase axis R₁ rows.length after ≤ windows.before := by
  intro ar dir t initial windows pp lp axis after rows tab labels hc he hr hl
  have level : (d₁)+1=CoverScale.initialDepth (Cube D) (r₁) (l+1) := Nat.sub_add_cancel (Nat.succ_pos _)
  obtain ⟨pack,shape⟩ := cal.locatedGateTable_shape grid qpos position initial
  have size := front_sizes shape
  have aligned := congrArg (fun d => CoverScale.sites (Cube D) (EnrichedOuter.depth S d T₁)) level.symm
  have cellFit := aligned.le.trans size.1
  have entryFit : dir.entries≤t.outputs := size.2
  have dirEq : dir=b.signedStartupDirectory (l+1) description := (grid.template_directory (pins₁) (geo₁)).2
  have actual := front initial description ceiling₁ l (size₁) header tiles J₁ t
  rw [←dirEq] at actual
  have room := (cal.locatedGateTable_routing grid qpos position chart reader chargeFit routing).2.1
  rw [t.reserved_size]
  exact actual cellFit entryFit pp lp axis after room.ceiling hc he hr hl

end Diagonal

end BorderVNP
end Computability
end OAI

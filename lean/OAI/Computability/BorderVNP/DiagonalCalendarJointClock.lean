import OAI.Computability.BorderVNP.DiagonalCalendarBootChecks
import OAI.Computability.BorderVNP.DiagonalDeployedJointClock
import OAI.Computability.BorderVNP.DiagonalCalendarTaskRoom

/-! # Joint time of the original prefixes on the selected calendar -/

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

set_option maxRecDepth 7000
set_option maxHeartbeats 3600000
set_option synthInstance.maxSize 4500

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


local notation3 (prettyPrint := false) "plan₁" => cal.seed.choose
local notation3 (prettyPrint := false) "W₁" => cal.frozenWitness
local notation3 (prettyPrint := false) "sites₁" => (Fintype.equivFin (((W₁).routedFine position).Site)).toEmbedding
local notation3 (prettyPrint := false) "edges₁" => (Fintype.equivFin (((W₁).routedFine position).Edge)).toEmbedding
local notation3 (prettyPrint := false) "ports₁" => (Fintype.equivFin (Fin (r₁) × Fin (publicWidth (tape₁)))).toEmbedding
local notation3 (prettyPrint := false) "number₁" => Fintype.equivFin (Cube D → Deck (EnrichedOuter.depth S (d₁+1) T₁+1))
local notation3 (prettyPrint := false) "tag₁" => ParseTable.signedLiteralCode (s:=size₁) ord
local notation3 (prettyPrint := false) "x₁" => fun _ : Unit => false


open RoutingISA.Evaluator RoutingISA.CompactMachine CellMacro.Generator TeamSite
local notation3 (prettyPrint := false) "P₁" => (signedProgram (cube.cubeID paid)).program
local notation3 (prettyPrint := false) "blank₁" => TimedProcessor.scaleData (P₁)
  (siteLibrary SparseExterior.driver) (fun _ : Fin 8 => some false) (geo₁)
  (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => false) (fun _ _ _ => false)
local notation3 (prettyPrint := false) "outside₁" => TeamScales.exterior (ξ₁) (r₁) (l+1)
local notation3 (prettyPrint := false) "table₁" => (located₁).raw.reserve ceiling₁
local notation3 (prettyPrint := false) "hold₁" => cal.frozenRouteBlock chart reader chargeFit

private theorem startupTeams_le_next (arena : StartupArena) (processors : 0<arena.processors) (link : 0<arena.link) :
    arena.teams ≤ arena.next := by
  have h : arena.teams-1 ≤ arena.stride := (Nat.le_mul_of_pos_right _ link).trans (Nat.le_add_left _ _)
  have h' : arena.stride ≤ arena.frame := Nat.le_mul_of_pos_left _ processors
  have room : arena.frame+112 ≤ arena.next := by
    dsimp only [StartupArena.next, StartupArena.hbase, StartupArena.ibase, StartupArena.broadcastBase, StartupArena.dense]
    omega
  omega

local notation "params₁" => pairedTableParameters (l+1) (size₁)
local notation "scalars₁" => Fintype.card (paid.Entry ⊕ BorderVNP.Cube.TableEntry cube.pred cube.b cube.h cube.copies cube.width)
local notation "public₁" => ⌈publicWork (cube.pred+1) scales.α (r₁) (l+1) (R₁+1)⌉₊
local notation "local₁" => ⌈localWork (cube.pred+1) (E+2) scales.α (ξ₁) (r₁) (l+1) (R₁+1)⌉₊
local notation "route₁" => 512*(cube.pred+1+BorderVNP.Cube.Tally.selectorWidth cube.pred cube.copies cube.h+1)
local notation3 (prettyPrint := false) "fixed₁" => (CubeConstants.install (cube.cubeID paid)).slots
local notation "argWidth" => BorderVNP.Cube.Tally.argumentWidth cube.pred cube.b cube.h cube.copies cube.width
local notation "finish₁" => ScheduleClock.cubeCoefficient cube.pred cube.b cube.h cube.copies cube.width argWidth
local notation "read₁" => BorderVNP.Cube.TeamRowClock.physicalCoefficient cube.pred cube.b cube.h cube.copies cube.width

include cal in
/-- The five windows use the actual team count and fit within the selected calendar clock. -/
theorem SignedCalendarAt.frozenPhaseCharges :
    scales.chosenSignedWindows cube E (l+1) r₁ =
      ScheduleClock.uniformWindows r₁ (R₁+1) outside₁ public₁ local₁ route₁ fixed₁ finish₁ read₁ ∧
      let c := scales.chosenSignedWindows cube E (l+1) r₁
      c.core+c.before+c.argumentsCalls+c.finish+c.reader ≤ TeamScales.ticks ξ₁ r₁ (l+1) := by
  refine ⟨?_,cal.time⟩
  unfold EpochScales.chosenSignedWindows EpochScales.signedWindows
  rw [(b.sizes (Nat.succ_pos l)).1]

/-- The five stage receipts are indexed by the actual calendar boot and the chosen
public clock. The name keeps the large original-site program shared. -/
noncomputable def SignedCalendarAt.FrozenJointClockRequest : Prop :=
  let bounds := cal.frozenBootBounds grid qpos position chart reader chargeFit
  let clock := cal.frozenSewnPacketClock grid qpos position chart reader chargeFit
  @ChosenReader.DeployedClockRequest F inferInstance D m
      (BorderVNP.Cube.TableEntry cube.pred cube.b cube.h cube.copies cube.width) inferInstance
      paid (φ ∘ cube.table) q l size₁ ord common chart inferInstance inferInstance
      R₁ r₁ w₁ (budget₁+6) _ a₁ ℓ₁ ec₁ axes d₁ reader prog₁ P₁ blank₁ (geo₁).fits order₁ W₁ position
      (Fintype.card (((W₁).routedFine position).Site)) (Fintype.card (((W₁).routedFine position).Edge))
      (Fintype.card (Fin (r₁) × Fin (publicWidth (tape₁)))) sites₁ edges₁ ports₁
      copies₁ ((fan S)^T₁) header layout₁ cap₁ (located₁).outputs w₁ table₁ task₁ outside₁ hold₁
      bounds.1 bounds.2.1 bounds.2.2.1 bounds.2.2.2.1 bounds.2.2.2.2.1 bounds.2.2.2.2.2.1
      bounds.2.2.2.2.2.2.1 clock public₁ local₁ route₁ fixed₁ finish₁ read₁

attribute [local irreducible] ChosenReader.DeployedClockRequest

set_option cleanup.letToHave false in
/-- On each original joint prefix, the authenticated early, argument and
post-call receipts charge its actual windows. All addresses and fixed
resource bounds refer to the same calendar boot as the sparse continuation. -/
theorem SignedCalendarAt.frozenJointClock
    (rectangle : 512*((R₁+1)+1)*(params₁+scalars₁+1)*(w₁+1)+(7+reader.charge) ≤ r₁) :
    cal.FrozenJointClockRequest grid qpos position chart reader chargeFit := by
  unfold FrozenJointClockRequest
  let bounds := cal.frozenBootBounds grid qpos position chart reader chargeFit
  let room := cal.frozenTask_room grid qpos position chart reader chargeFit
  let clock := cal.frozenSewnPacketClock grid qpos position chart reader chargeFit
  have positiveCharge : 0 < 7+reader.charge :=
    (by decide : 0<7).trans_le (Nat.le_add_right _ _)
  have processors : 0<r₁ := positiveCharge.trans_le ((Nat.le_add_left _ _).trans rectangle)
  have teamFit : R₁+1<2^w₁ :=
    (startupTeams_le_next (initial₁) processors (grid.block_pos.trans_le (grid.block_le.trans_eq grid.link_eq))).trans_lt
      bounds.2.2.1
  have parCount : (task₁).p.parameters=params₁ := rfl
  have scalarCount : scalars₁=(task₁).p.report.gadgets := rfl
  have teamCount : (task₁).cube.teams=R₁+1 := rfl
  exact @ChosenReader.deployedFrozenSites_clockRequest F inferInstance D m
      (BorderVNP.Cube.TableEntry cube.pred cube.b cube.h cube.copies cube.width) inferInstance
      paid (φ ∘ cube.table) q l size₁ ord common chart inferInstance inferInstance
      R₁ r₁ w₁ (budget₁+6) _ a₁ ℓ₁ ec₁ axes d₁ reader prog₁ P₁ blank₁ (geo₁).fits order₁ W₁ position
      (Fintype.card (((W₁).routedFine position).Site)) (Fintype.card (((W₁).routedFine position).Edge))
      (Fintype.card (Fin (r₁) × Fin (publicWidth (tape₁)))) sites₁ edges₁ ports₁
      copies₁ ((fan S)^T₁) header layout₁ cap₁ (located₁).outputs w₁ table₁ task₁ outside₁ hold₁
      bounds.1 bounds.2.1 bounds.2.2.1 bounds.2.2.2.1 bounds.2.2.2.2.1 bounds.2.2.2.2.2.1
      bounds.2.2.2.2.2.2.1 clock parCount scalarCount teamCount teamFit room.2.2.1 room.2.1 rectangle public₁ local₁ route₁ fixed₁ finish₁ read₁

end Diagonal

end BorderVNP
end Computability
end OAI

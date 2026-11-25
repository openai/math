import OAI.Computability.BorderVNP.DiagonalCalendarDeployment

/-! # Memory bounds on the installed signed task -/

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

local notation "par₁" => pairedTableParameters (l+1) (size₁)
local notation "cubeEntries" => _root_.OAI.Computability.BorderVNP.Cube.TableEntry cube.pred cube.b cube.h cube.copies cube.width
local notation "gadgets" => Fintype.card (paid.Entry ⊕ cubeEntries)
local notation "query₁" => Fintype.card (Board.Physical (par₁) (budget₁+6) w₁ (paid.Entry ⊕ cubeEntries))
local notation "guess₁" => Fintype.card (Guess (Fin (par₁)) reader.gridRank (Nat.clog 2 common.p+1) (Nat.clog 2 common.p))

/-- The field task and its three reader banks satisfy the actual startup
bounds on this frozen deployment, including the inverse-bank writes. -/
theorem SignedCalendarAt.frozenTask_room :
    let task := cal.frozenTask grid qpos position chart reader chargeFit
    let raw := SignedTaskArena.rawAddress (initial₁) cap₁ cube.pred
      task.cube.header.d task.cube.header.cap
    task.ScalarRoom w₁ query₁ guess₁ reader.gates (addr*(r₁*(l+1)+1)^power) ∧
    task.endAddress w₁ query₁ guess₁ reader.gates < 2^w₁ ∧
    (initial₁).next ≤ task.cube.header.header ∧ raw+(R₁+1)*(par₁+gadgets)*w₁=(initial₁).ibase ∧
    (initial₁).frame+30 < 2^w₁ ∧ (initial₁).ibase+(par₁+2)*(budget₁+6) ≤ task.tallyBits ∧
    (initial₁).hbase+(par₁+2)*(budget₁+6) ≤ task.tallyBits ∧
    (initial₁).dense+(6+3*reader.gates+query₁)*w₁ ≤ task.tallyBits := by
  let chosen := located₁
  let L := cal.frozenLayout chart reader chargeFit
  have paidBits : GeometryAdviceRate.packetWords ceiling₁ cap₁ chosen.outputs w₁ * w₁ ≤
      r₁*TeamScales.width (l+1) (95/100:ℝ) := (Nat.le_add_left _ _).trans chosen.packet_bound
  have wordPos : 1 ≤ w₁ := grid.word_eq.symm ▸ Nat.pow_pos grid.log_pos
  have ok := cal.task l rfl chart reader chargeFit description ceiling₁ chosen.outputs w₁ chosen.directories wordPos paidBits
  have arena := reader.frozenTask_startupArena (geo₁) (ℓ₁) L.header
  have headerEq := (cal.frozenLayout_fields chart reader chargeFit).1
  conv_rhs at arena => rw [headerEq,←grid.link_eq]
  have dirEq := (grid.template_directory (pins₁) (geo₁)).2
  let contract (initial : StartupArena) (directory : Directory.Layout) : Prop :=
    let task := b.frozenSignedTask cube (l+1) l (size₁) header initial directory cap₁ ceiling₁
      chosen.outputs w₁ chosen.directories
    let raw := SignedTaskArena.rawAddress initial cap₁ cube.pred task.cube.header.d task.cube.header.cap
    task.ScalarRoom w₁ query₁ guess₁ reader.gates (addr*(r₁*(l+1)+1)^power) ∧
      task.endAddress w₁ query₁ guess₁ reader.gates < 2^w₁ ∧
      initial.next ≤ task.cube.header.header ∧ raw+(R₁+1)*(par₁+gadgets)*w₁=initial.ibase ∧
      initial.frame+30 < 2^w₁ ∧ initial.ibase+(par₁+2)*(budget₁+6) ≤ task.tallyBits ∧
      initial.hbase+(par₁+2)*(budget₁+6) ≤ task.tallyBits ∧
      initial.dense+(6+3*reader.gates+query₁)*w₁ ≤ task.tallyBits
  exact (congrArg₂ contract arena dirEq).mpr ok

end Diagonal

end BorderVNP
end Computability
end OAI

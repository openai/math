import OAI.Computability.BorderVNP.DiagonalFrozenCalendarWitness
import OAI.Computability.BorderVNP.DiagonalLocatedSignedGrid
import OAI.Computability.BorderVNP.DiagonalFrozenSignedDeployment

/-! # The physical signed deployment on the selected calendar -/

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

/-- The charged table uses the calendar's original query network, actual
epoch plan and signed cube. Every valid public history is assigned after
this table and its ordinary or marker addresses are fixed. -/
noncomputable def SignedCalendarAt.locatedGateTable (initial : StartupArena) :
    SeedPlan.LocatedFrozenTable cap₁ w₁ ceiling₁ (l+1) r₁ (R₁+1) tiles J₁ (fun gates o =>
      SignedTableStartupAt (aux:=φ ∘ cube.table) (q:=q) cube b (prog₁) adv c charge factor (l+1)
        gates ceiling₁ ceiling₁ o w₁ description) := by
  let plan := cal.seed.choose
  let wr := cal.seed.choose_spec.choose
  let fit := cal.seed.choose_spec.choose_spec
  have literal := (grid.template_directory (pins₁) (geo₁)).1
  have inputs := grid.packet_inputs φ q adv c charge factor coeff cal.output (tape₁) literal grid.link_eq.symm
    (order₁) position description
  exact plan.locatedFrozenTable (tape₁) (order₁) position cal.frozenWitness cube b initial l (size₁) coeff
    wr hm fit.2.1 grid.count qpos grid.log_pos grid.word_eq grid.block_pos (grid.block_le.trans_eq grid.link_eq)
    grid.sites_pos inputs cal.output.1 φ q adv c charge factor rfl cal.output.2.1

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

/-- The selected task starts above the actual measured packet and both
original-bundle arrays. Its descriptor and inverse permutations are exactly
the directories assigned before the selected wire table is serialized. -/
noncomputable def SignedCalendarAt.frozenTask : SignedTaskArena.Layout := task₁

/-- The genuine site literal, reference packet and public gate program on all
teams of the selected batch. The sorted bundle directories and the original
verifier literal precede every assignment of the column, pin or shared history. -/
noncomputable def SignedCalendarAt.frozenSites : SiteData (R₁) (r₁) 64 32 (w₁) (a₁) := by
  classical
  let W := cal.frozenWitness
  let named := W.routedFine position
  let sites := (Fintype.equivFin named.Site).toEmbedding
  let edges := (Fintype.equivFin named.Edge).toEmbedding
  let ports := (Fintype.equivFin (Fin (r₁) × Fin (publicWidth (tape₁)))).toEmbedding
  let P := (withStartup (signedBody (cube.cubeID paid))).program
  let blank := TimedProcessor.scaleData (signedProgram (cube.cubeID paid)).program (siteLibrary SparseExterior.driver)
    (fun _ : Fin 8 => some false) (geo₁) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => false) (fun _ _ _ => false)
  exact reader.deployedFrozenSites (prog₁) P blank (geo₁).fits W position sites edges ports (copies₁)
    ((fan S)^T₁) header (layout₁) ((located₁).raw.reserve ceiling₁) (task₁) (TeamScales.exterior (ξ₁) (r₁) (l+1))

end Diagonal

end BorderVNP
end Computability
end OAI

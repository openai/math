import OAI.Computability.BorderVNP.DiagonalCalendarFrozenBoots
import OAI.Computability.BorderVNP.DiagonalSignedBareHeaderReceipts

/-! # Header-copy returns on the actual selected calendar boot -/

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


local notation3 (prettyPrint := false) "physical₁" => cal.frozenSites grid qpos position chart reader chargeFit
local notation3 (prettyPrint := false) "program₁" => (withStartup (signedBody (cube.cubeID paid))).program
local notation3 (prettyPrint := false) "wired₁" => wiringWith (prog₁) (program₁) physical₁ (pins₁) (ℓ₁) (l+1) ec₁ (geo₁).fits
local notation3 (prettyPrint := false) "names₁" => (cal.frozenWitness).routedFine position
local notation3 (prettyPrint := false) "sites₁" => (Fintype.equivFin (names₁).Site).toEmbedding
local notation3 (prettyPrint := false) "edges₁" => (Fintype.equivFin (names₁).Edge).toEmbedding
local notation3 (prettyPrint := false) "ports₁" => (Fintype.equivFin (Fin (r₁) × Fin (publicWidth (tape₁)))).toEmbedding
local notation3 (prettyPrint := false) "tag₁" => ParseTable.signedLiteralCode (s:=size₁) ord
local notation3 (prettyPrint := false) "selectedTask" => cal.frozenTask grid qpos position chart reader chargeFit
local notation3 (prettyPrint := false) "selectedSites" => cal.frozenSites grid qpos position chart reader chargeFit
local notation3 (prettyPrint := false) "table₁" => (located₁).raw.reserve ceiling₁
local notation "outside₁" => TeamScales.exterior (ξ₁) (r₁) (l+1)
local notation3 (prettyPrint := false) "directory₁" => freeDirectory R₁ r₁ (initial₁).literal ℓ₁ tiles
  (GridHosts.inputBlockWidth r₁ (l+1) axes d₁) J₁ description
local notation3 (prettyPrint := false) "fresh₁" => (initial₁).next+7*(directory₁).candidates
local notation3 (prettyPrint := false) "origin₁" =>
  Allocation.dest fresh₁ cap₁ (table₁).size (located₁).outputs w₁
local notation3 (prettyPrint := false) "route₁" => routingExtension (signedBudgetWords w₁ outside₁)
  directory₁ origin₁ (selectedTask).cube.cables (selectedTask).cube.cells
local notation3 (prettyPrint := false) "placed₁" u => reader.frozenTaskPlacement selectedTask initial₁ u route₁
local notation3 (prettyPrint := false) "pin₁" u => CubeHeaderInstall.pinFields (placed₁ u).extension
  (Allocation.stop fresh₁ cap₁ (table₁).size (located₁).outputs w₁ w₁) (selectedTask).cube.header.d
  ((selectedTask).cube.n+1) ((selectedTask).cube.h*(selectedTask).cube.b) (selectedTask).cube.header.blocks cap₁
  (BorderVNP.Cube.Physical.declarationCap (selectedTask).cube.n (selectedTask).cube.header.d
    (selectedTask).cube.header.blocks (selectedTask).cube.b (selectedTask).cube.h (selectedTask).cube.s)
local notation3 (prettyPrint := false) "stripe₁" => GeometryAdviceRate.stripeWidth
  (GeometryOutput.packetCount cap₁ (table₁).size (located₁).outputs w₁*w₁) r₁
local notation3 (prettyPrint := false) "fields₁" u => Allocation.fields (pin₁ u) fresh₁ cap₁ (table₁).size
  (located₁).outputs w₁ ((initial₁).literal/4) stripe₁
local notation3 (prettyPrint := false) "packet₁" u => reader.packetAt (ReaderPlacement.inArena initial₁
  (placed₁ u).valuation (placed₁ u).entry (placed₁ u).totals (fields₁ u))


local notation3 (prettyPrint := false) "ad₁" => adviceOffsetWith (prog₁) r₁ 32 64 w₁ (l+1)
local notation3 (prettyPrint := false) "headers₁" => JointHeader.PositiveFields cap₁ (selectedTask).cube.n
  (selectedTask).cube.header.d (selectedTask).cube.header.cap (R₁+1) (selectedTask).dim (b.physical.tally (l+1))
local notation3 (prettyPrint := false) "seedStrings" => (cal.frozenWitness).seedLiteralMatrix position tag₁ sites₁ edges₁ ports₁
  copies₁ ((fan S)^T₁) (header*logWidth (r₁) (l+1))


open TeamContraction.JointHeader

local notation3 (prettyPrint := false) "address₁" => fun u : Fin (R₁+1) => (initial₁).unitAddresses ad₁ (packet₁ u)
local notation3 (prettyPrint := false) "frame₁" u => (wired₁).transferFrame u (layout₁).header (initial₁).broadcastBase
local notation "first₁" => freeStartWith prog₁ r₁ 32 64 w₁ (l+1)
local notation3 (prettyPrint := false) "stripeStart" => Allocation.stripe fresh₁ cap₁ (table₁).size (located₁).outputs w₁
  ((initial₁).literal/4) stripe₁
local notation3 (prettyPrint := false) "bits₁" => GeometryAdvice.serialized (GeometryAdvice.packet (w:=w₁) fresh₁
  (Allocation.packed fresh₁ cap₁ (table₁).size (located₁).outputs w₁ w₁) table₁
  (fun i => (initial₁).broadcastBase+1+Fin.val i))
local notation3 (prettyPrint := false) "raw₁" => SignedTaskArena.rawAddress initial₁ (selectedTask).cube.header.profile
  (selectedTask).cube.n (selectedTask).cube.header.d (selectedTask).cube.header.cap
local notation3 (prettyPrint := false) "full₁" u => signedProfileExtension selectedTask (signedBudgetWords w₁ outside₁)
  directory₁ origin₁ (selectedTask).cube.cables (selectedTask).cube.cells raw₁ (Fin.val u) w₁ fresh₁ cap₁
  (table₁).size (located₁).outputs w₁ ((initial₁).literal/4) stripe₁


open private next_lt_stop from OAI.Computability.BorderVNP.DiagonalCalendarFrozenBoots

set_option maxHeartbeats 16500000 in
set_option maxRecDepth 12500 in
/-- Split each chosen boot at its header-copy instruction. The returned header
and the preceding startup trace use this exterior's initial pin fields. -/
theorem SignedCalendarAt.frozenHeaderCopyTraces (fixed : Routing.Block (R₁+1))
    (live : Fin pins₁ → Bool) (p : headers₁) (wire : HeaderExterior layout₁ p.bits) :
    let chosen := cal.frozenSites_boots grid qpos position chart reader chargeFit fixed
    ∃ (positive : PositiveExterior wired₁ address₁ live w₁ wire.val) (h : ReturnedHeaders wired₁ live wire.val layout₁ w₁),
      h.ibase=(fun u => ((address₁) u).ibase) ∧ h.hbase=(fun u => ((address₁) u).hbase) ∧
      h.starbase=(fun u => ((address₁) u).starbase) ∧ h.dest=(fun u => ((address₁) u).dst) ∧
      ∀ u, let node := chosen.2.choose live ⟨wire.val,positive⟩ u
        let ad := (address₁) u
        let F := (wired₁).processorFields u live wire.val ad.ibase ad.hbase ad.starbase
        ∃ before : List (TeamRAM.Event w₁), Runs ((physical₁).publicWords u)
          (TeamSiteEvents.macros (w:=w₁) (siteLibrary SparseExterior.driver) (nativeClock (l+1))) unitStartup
          ((physical₁).registers u) (processorMemory F w₁) before (h.regs u) (h.input u) ∧
          node.trace=before++(h.returned u).val.1 ∧ (h.returned u).val.2=(node.out,node.memory) ∧
          FlatAt (h.returned u).val.2.2 ad.dst p.bits := by
  let blank := TimedProcessor.scaleData (signedProgram (cube.cubeID paid)).program (siteLibrary SparseExterior.driver)
    (fun _ : Fin 8 => some false) (geo₁) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => false) (fun _ _ _ => false)
  let room := cal.frozenSourceRoom grid qpos position chart reader chargeFit
  have hw : 0 < w₁ := grid.word_eq.symm ▸ Nat.pow_pos grid.log_pos
  exact reader.deployed_header_receipts prog₁ program₁ blank (geo₁).fits cal.frozenWitness position sites₁ edges₁ ports₁
    copies₁ ((fan S)^T₁) header layout₁ table₁ selectedTask outside₁ fixed
    room.2.2.2.1 room.2.1 (next_lt_stop room.2.2.2.2.1) hw (layout₁).three room.2.2.1
    (by have bounds := (layout₁).fits fixed; omega) (fun _ => cal.frozen_unit_clock chart reader chargeFit)
    (cal.frozenLayout_fields chart reader chargeFit).1 live p wire

/-- The native header copies for every team of a fixed exterior, before
choosing a joint prefix or performing any private calls. -/
noncomputable def SignedCalendarAt.frozenHeaderCopies (fixed : Routing.Block (R₁+1))
    (live : Fin pins₁ → Bool) (p : headers₁) (wire : HeaderExterior layout₁ p.bits) :
    ReturnedHeaders wired₁ live wire.val layout₁ w₁ :=
  (cal.frozenHeaderCopyTraces grid qpos position chart reader chargeFit fixed live p wire).choose_spec.choose

end Diagonal

end BorderVNP
end Computability
end OAI

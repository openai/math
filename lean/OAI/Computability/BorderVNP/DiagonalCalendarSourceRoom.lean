import OAI.Computability.BorderVNP.DiagonalCalendarDeployment

/-! # The complete timed source rectangle of the selected signed table and reader -/

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

open GeometryAdviceRate TeamContraction.JointHeader Cube.Physical

/-- The actual signed witnesses, reader and raw table determine a single
fixed source rectangle. The scheduler fits both stripes, the full private
description tail and every site reconstruction on its allocated clock. -/
theorem SignedCalendarAt.frozenSourceRoom :
    let chosen := cal.locatedGateTable grid qpos position initial₁
    let t := chosen.raw.reserve ceiling₁
    let area := initial₁
    let directory := freeDirectory R₁ r₁ area.literal ℓ₁ tiles (GridHosts.inputBlockWidth r₁ (l+1) axes d₁) J₁ description
    let first := freeStartWith prog₁ r₁ 32 64 w₁ (l+1)
    let fresh := area.next+7*directory.candidates
    let width := GeometryAdviceRate.stripeWidth (GeometryOutput.packetCount cap₁ t.size chosen.outputs w₁*w₁) r₁
    let stripe := Allocation.stripe fresh cap₁ t.size chosen.outputs w₁ (area.literal/4) width
    let small := seedBoxCapacity (l+1) r₁ axes d₁ (Fintype.card (Direction axes))
    directory=dir₁ ∧ reader.packetBitCount≤r₁ ∧ 0<(layout₁).header ∧
      JointRoom directory first a₁ (signedBootStripe first) stripe ∧
      Allocation.stop fresh cap₁ t.size chosen.outputs w₁ w₁<2^w₁ ∧
      0<directory.literal/2 ∧ small≤l+1 ∧ description≤l+1 ∧ description≤directory.literal/2 ∧
      J₁*description≤(R₁+1)*r₁*(directory.literal/2) ∧
      ∀ (loc : ReaderPlacement w₁) (f : BroadcastFrame) (frame : ℕ), f.Fits w₁ frame →
        f.processors=r₁ → f.teams=R₁+1 → f.link=ℓ₁ →
        factor*(jointBudget (reader.packetAt loc).bits.length w₁+f.readTicks+2+
          ((pinSetup.slots+17*(r₁*directory.literal)+1)+GeometryAdviceRate.ticks t.size cap₁ chosen.outputs w₁ w₁))
          ≤ TeamScales.ticks ξ₁ r₁ (l+1) := by
  intro chosen t area directory first fresh width stripe small
  have installed := chosen.startup chart reader chargeFit
  obtain ⟨_,_,replica,_,room,bound,time⟩ := installed
  have literal := (grid.template_directory pins₁ geo₁).1
  have reference := (grid.template_directory pins₁ geo₁).2
  have original := reader.frozenTask_startupArena geo₁ ℓ₁ (layout₁).header
  have fields := cal.frozenLayout_fields chart reader chargeFit
  have lit : area.literal=TeamScales.literal scales.α (l+1) := congrArg StartupArena.literal original
  have same : directory=dir₁ := by dsimp only [directory]; rw [lit,literal]
  have canonical : directory=b.signedStartupDirectory (l+1) description := same.trans reference
  let makeArea (length header : ℕ) := (⟨R₁+1,r₁,TeamScales.literal scales.α (l+1),length,header,reader.packetBitCount⟩ : StartupArena)
  have equalArea := congrArg₂ makeArea grid.link_eq.symm fields.1
  have arEq := original.trans equalArea
  have nextEq : area.next = (makeArea (b.physical.link (l+1)) _).next := congrArg StartupArena.next arEq
  have paid : t.size=ceiling₁ := chosen.reserved_size
  have raw := grid.literalRanges
  have sizeBounds : 0<directory.literal/2 ∧ small≤l+1 ∧ description≤l+1 ∧ description≤directory.literal/2 ∧
      J₁*description≤(R₁+1)*r₁*(directory.literal/2) := by
    change 0<area.literal/2 ∧ small≤l+1 ∧ description≤l+1 ∧ description≤area.literal/2 ∧
      J₁*description≤(R₁+1)*r₁*(area.literal/2)
    rw [lit]
    exact raw
  refine ⟨same,replica,fields.2.1,?_,?_,sizeBounds.1,sizeBounds.2.1,sizeBounds.2.2.1,sizeBounds.2.2.2.1,sizeBounds.2.2.2.2,?_⟩
  · dsimp only [stripe,fresh,width]
    rw [paid,nextEq,canonical,lit]
    exact room
  · dsimp only [fresh]
    rw [paid,nextEq,canonical]
    exact bound
  · intro loc f frame fit rEq teams link
    rw [paid]
    change _*(jointBudget _ _+f.readTicks+2+((pinSetup.slots+17*(r₁*area.literal)+1)+_))≤_
    rw [lit]
    exact time loc f frame fit rEq teams link

end Diagonal

end BorderVNP
end Computability
end OAI

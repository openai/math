import OAI.Computability.BorderVNP.DiagonalCalendarLocatedEmitter
import OAI.Computability.BorderVNP.DiagonalCalendarFrozenBoots
import OAI.Computability.BorderVNP.DiagonalCalendarBootChecks
import OAI.Computability.BorderVNP.DiagonalInstalledTableHistories

/-! # Decoding a returned public history at the signed calendar's actual boot -/

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


open Packing.Inherited Packing.Inherited.FrozenTape Shortening.PublicCapacity BorderVNP.Epoch.Round Cover
open EnrichedOuter

attribute [local instance] portFintype
local notation3 (prettyPrint := false) "plan₁" => cal.seed.choose
local notation3 (prettyPrint := false) "wr₁" => cal.seed.choose_spec.choose

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


local notation3 (prettyPrint := false) "program₁" => (withStartup (signedBody (cube.cubeID paid))).program
local notation3 (prettyPrint := false) "names₁" => (cal.frozenWitness).routedFine position
local notation3 (prettyPrint := false) "sites₁" => (Fintype.equivFin (names₁).Site).toEmbedding
local notation3 (prettyPrint := false) "edges₁" => (Fintype.equivFin (names₁).Edge).toEmbedding
local notation3 (prettyPrint := false) "ports₁" => (Fintype.equivFin (Fin (r₁) × Fin (publicWidth (tape₁)))).toEmbedding
local notation3 (prettyPrint := false) "x₁" => fun _ : Unit => false
local notation3 (prettyPrint := false) "base₁" => (plan₁).frozenStart (tape₁) (order₁) position Unit
local notation3 (prettyPrint := false) "widths₁" => fun i => Fintype.card (Machine.Guess S (d₁+1)
  (fun _ _ => 60*logWidth (r₁) (l+1)) i)
local notation3 (prettyPrint := false) "slots₁" => fun i => Fintype.equivFin (Machine.Guess S (d₁+1)
  (fun _ _ => 60*logWidth (r₁) (l+1)) i)
local notation3 (prettyPrint := false) "head₁" => WorkWords.grouped (CoverScale.sites (Cube D) (d₁+1))
  (copies₁*GridHosts.inputBlockWidth (r₁) (l+1) axes d₁)
local notation3 (prettyPrint := false) "key₁" => Equiv.toEmbedding (finCongr (seedPortCount (D:=D) d₁))
local notation3 (prettyPrint := false) "fmt₁" => Boundary.seedFormat (tape₁) (order₁) position copies₁
local notation3 (prettyPrint := false) "steps₁" => (plan₁).compiled.tapeSteps (fmt₁) (head₁) (key₁) wr₁ hm
local notation3 (prettyPrint := false) "hist₁" => compile steps₁ T₁ le_rfl (repeatLeaf (fan S) base₁ T₁)
local notation3 (prettyPrint := false) "fit₁" => (plan₁).profile_order_fits widths₁ slots₁
local notation3 (prettyPrint := false) "readOrder" => broadcastOrder (fan S) widths₁ slots₁ T₁

attribute [local irreducible] Nat.clog UniversalMachine.programPrefix
open TeamContraction.JointHeader
local notation3 (prettyPrint := false) "early" => cal.locatedEmitter grid position initial₁ tape₁
local notation3 (prettyPrint := false) "fixed₁" => cal.frozenRouteBlock chart reader chargeFit
local notation3 (prettyPrint := false) "chosen₁" => cal.frozenSites_boots grid qpos position chart reader chargeFit fixed₁
local notation3 (prettyPrint := false) "outside₁" => TeamScales.exterior ξ₁ r₁ (l+1)
local notation3 (prettyPrint := false) "nativeDir" => freeDirectory R₁ r₁ (initial₁).literal ℓ₁ tiles
  (GridHosts.inputBlockWidth r₁ (l+1) axes d₁) J₁ description
local notation3 (prettyPrint := false) "fresh₁" => (initial₁).next+7*(nativeDir).candidates

/-- The initialized table is exactly the original native lowering padded to
the geometry ceiling. -/
theorem SignedCalendarAt.frozenDecoderTable :
    (located₁).raw.reserve ceiling₁ =
      reservedGeometryTable hist₁ readOrder fit₁ (early).emitter x₁ ceiling₁ := rfl

include qpos in
/-- The public gate test on the initial named template is precisely the
test lowered into the table of the signed calendar. -/
theorem SignedCalendarAt.frozenDecoderGateFit :
    (geometryTable hist₁ readOrder fit₁ (early).emitter x₁).size ≤ ceiling₁ :=
  (located₁).raw_bound

/-- Every structured header in the chosen physical wire layout has exactly
the declared length of this calendar's installed task. -/
theorem SignedCalendarAt.frozenDecoderHeaderWidth :
    (layout₁).header = PositiveFields.width cap₁ (task₁).cube.n (task₁).cube.header.d
      (task₁).cube.header.cap (R₁+1) (task₁).dim w₁ :=
  (cal.frozenLayout_fields chart reader chargeFit).1

include qpos in
/-- At the calendar's reserved gate ceiling the last header and packet
fields fit below the native address-space limit. -/
theorem SignedCalendarAt.frozenDecoderEnd :
    Allocation.stop fresh₁ cap₁ ceiling₁ (early).outputs w₁ w₁ < 2^w₁ := by
  let room := cal.frozenSourceRoom grid qpos position chart reader chargeFit
  calc
    _ = Allocation.stop fresh₁ cap₁ ((located₁).raw.reserve ceiling₁).size (early).outputs w₁ w₁ :=
      congrArg (fun z => Allocation.stop fresh₁ cap₁ z (early).outputs w₁ w₁) (located₁).reserved_size.symm
    _ < _ := room.2.2.2.2.1

set_option maxHeartbeats 4200000 in
/-- For the actual booted pin of the signed evaluator, all and only genuinely
returned public words decode into original frozen histories. The boot family
here is the very family used by the issued positive cell execution. -/
noncomputable def SignedCalendarAt.frozenIssuedHistoryDecoder
    (values : (seedBundle (tape₁) axes d₁ (order₁) position copies₁).Tables F)
    (pin : Fin ((pairedTableParameters (l+1) (stretch b.σ (l+1))+2)*(adv (adviceScale b.σ b.ρ (l+1))+6)) → Bool) :=
  let blank := TimedProcessor.scaleData (signedProgram (cube.cubeID paid)).program (siteLibrary SparseExterior.driver)
    (fun _ : Fin 8 => some false) (geo₁) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => false) (fun _ _ _ => false)
  let room := cal.frozenSourceRoom grid qpos position chart reader chargeFit
  let chosen := chosen₁
  reader.installedSupportedPreparations (R:=R₁) (r:=r₁) (rw:=w₁) (pinWidth:=budget₁+6)
    (a:=a₁) (link:=ℓ₁) (ec:=ec₁) (d:=d₁) (gridOrder:=order₁) (copies:=copies₁) (headerFactor:=header)
    (T:=T₁) (Q:=Q) (reserve:=cap₁) (o:=(located₁).outputs) (field:=w₁)
    (prog₁) (program₁) blank (geo₁).fits cal.frozenWitness position sites₁ edges₁ ports₁
    (plan₁) (layout₁) x₁ values wr₁ hm widths₁ slots₁ fit₁ (early).emitter
    (8*(11920000+1500000+16008100*coeff+37)) (4*(E+2)) ((located₁).raw.reserve ceiling₁) (task₁) outside₁
    (cal.frozenDecoderTable grid qpos position chart reader chargeFit)
    (cal.frozenDecoderGateFit grid qpos position chart reader chargeFit)
    (cal.frozenDecoderHeaderWidth grid qpos position chart reader chargeFit)
    pin room.2.2.2.1 room.2.1 le_rfl (cal.frozenDecoderEnd grid qpos position chart reader chargeFit) fixed₁
    (grid.word_eq.symm ▸ Nat.pow_pos grid.log_pos) (fun u => (chosen.1 u).1) (chosen.2.choose pin)

end Diagonal

end BorderVNP
end Computability
end OAI

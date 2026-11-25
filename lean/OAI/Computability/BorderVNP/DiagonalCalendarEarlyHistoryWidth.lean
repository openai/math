import OAI.Computability.BorderVNP.DiagonalCalendarPlacementExtents
import OAI.Computability.BorderVNP.DiagonalCalendarHistoryWidth
import OAI.Computability.BorderVNP.PackedTerminalSignedHosts
import OAI.Computability.BorderVNP.DiagonalExternalSewFieldImage
import OAI.Computability.BorderVNP.PackedFrozenTapedInstallation

/-! # The initial physical network of an issued calendar history -/

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
set_option maxHeartbeats 5000000
attribute [local irreducible] Nat.clog Fintype.card Finset.univ

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


open Packing.Inherited Packing.Inherited.FrozenTape Shortening.PublicCapacity BorderVNP.Epoch.Round Cover
open EnrichedOuter Diagonal.CellEntries

attribute [local instance] portFintype
local notation3 (prettyPrint := false) "plan₁" => cal.seed.choose
variable {ord : Fin (l+1) × Bool ≃ Fin (2*(l+1))}
    {common : CommonField paid (φ ∘ cube.table) q l (stretch b.σ (l+1)) ord}
    (chart : AdvisedBranch common) [Fact common.p.Prime] [Algebra (ZMod common.p) chart.E]
    (reader : ChosenReader chart (b.physical.teamsPred (l+1)+1) (stretch b.ρ (l+1))
      (b.physical.multBits (l+1)) (b.physical.tally (l+1)) (b.physical.word (l+1))
      (adv (adviceScale b.σ b.ρ (l+1))+6))
    (chargeFit : reader.charge ≤ c*(adv (adviceScale b.σ b.ρ (l+1))+1)^charge)


local notation3 (prettyPrint := false) "program₁" => (withStartup (signedBody (cube.cubeID paid))).program
local notation3 (prettyPrint := false) "names₁" => (cal.frozenWitness).routedFine position
local notation3 (prettyPrint := false) "sites₁" => (Fintype.equivFin (names₁).Site).toEmbedding
local notation3 (prettyPrint := false) "edges₁" => (Fintype.equivFin (names₁).Edge).toEmbedding
local notation3 (prettyPrint := false) "ports₁" => (Fintype.equivFin (Fin (r₁) × Fin (publicWidth (tape₁)))).toEmbedding
local notation3 (prettyPrint := false) "tag₁" => ParseTable.signedLiteralCode (s:=size₁) ord
local notation3 (prettyPrint := false) "x₁" => fun _ : Unit => false

local notation3 (prettyPrint := false) "seed₁[" v "]" => (plan₁).frozenLeaf (tape₁) (order₁) position
  cal.frozenWitness tag₁ sites₁ edges₁ ports₁ v x₁
local notation3 (prettyPrint := false) "owners₁" => Fintype.equivFin (Cube D → Deck (EnrichedOuter.depth S (d₁+1) T₁+1))
local notation3 (prettyPrint := false) "stageAt[" v "," h "]" => ((packHistory (seed₁[v]) (plan₁).compiled.machine.epoch T₁).term h).val

local notation3 (prettyPrint := false) "blank₁" => TimedProcessor.scaleData (signedProgram (cube.cubeID paid)).program
  (siteLibrary SparseExterior.driver) (fun _ : Fin 8 => some false) (geo₁)
  (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => false) (fun _ _ _ => false)
local notation3 (prettyPrint := false) "originalWire" => wiringWith (prog₁) (program₁) blank₁ (pins₁) (ℓ₁) (l+1) ec₁ (geo₁).fits
local notation "outside" => TeamScales.exterior ξ₁ r₁ (l+1)

/-- The native source rows on the initial physical wiring use the original
terminal block hosts. The sparse width of their crossings therefore fits the chosen
exterior clock. -/
theorem SignedCalendarAt.frozenEarlyHistoryWidth
    (routing : LocatedFrozenRoutingAt cube b φ q adv c charge (l+1))
    (values : (seedBundle (tape₁) axes d₁ (order₁) position copies₁).Tables F)
    (history : (packHistory (seed₁[values]) (plan₁).compiled.machine.epoch T₁).Index) :
    let state := stageAt[values,history]
    let before := (Shortening.Adaptive.flattenPack T₁ state.pack).layout
    let attached := GridHosts.attachedHosts originalWire Fintype.card_pos grid.count before
    let params : FieldExport.Params := ⟨R₁,r₁,(originalWire).program.length+(cutWidth (l+1)+extra₁),
      ℓ₁,GridHosts.inputBlockWidth r₁ (l+1) axes d₁,tiles⟩
    let net := FieldExport.finalLayout params attached
    let cell := fun v : net.Site => owners₁ (reduceMove (EnrichedOuter.depth S (d₁+1) T₁) (state.route.origin v))
    intercellWidth net cell ≤ 2*(R₁+1)*outside := by
  intro state before attached params
  have installed := ((plan₁).frozen_leaf_installed tape₁ order₁ position cal.frozenWitness tag₁ sites₁ edges₁ ports₁
    values x₁).trans (CellEntries.SewnTape.native_grid_installed (R:=R₁) (r:=r₁) (copies:=copies₁) (pins:=pins₁)
      order₁ position prog₁ program₁ blank₁ (geo₁).fits)
  have same := enrichedBlockHosts_attached originalWire axes d₁ order₁ position grid.count
    (plan₁).compiled.machine (seed₁[values]) installed history
  let literal := (blank₁).enrichedFree prog₁ program₁ (l+1) ec₁ ℓ₁
  have widths : (plan₁).SewnWidths grid.count ℓ₁ outside (1/2) :=
    (congrArg (fun link => (plan₁).SewnWidths grid.count link outside (1/2)) grid.link_eq).mp
      (routing.sewn header Q (plan₁)).choose_spec
  have sparse := (plan₁).frozen_signed_intercell_width prog₁ (geo₁).fits cal.frozenWitness position tag₁
    sites₁ edges₁ ports₁ values x₁ literal grid.count widths history owners₁
  dsimp only [attached]
  rw [same]
  exact sparse.trans (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ (by decide : 0<2)))

end Diagonal

end BorderVNP
end Computability
end OAI

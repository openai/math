import OAI.Computability.BorderVNP.DiagonalCalendarIssuedExecution
import OAI.Computability.BorderVNP.DiagonalCalendarFrozenRealization
import OAI.Computability.BorderVNP.DiagonalSelectedRunAsEnriched

/-! # Completing the actual calendar deployment on its issued native cells -/

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
variable {ord : Fin (l+1) × Bool ≃ Fin (2*(l+1))}
    {common : CommonField paid (φ ∘ cube.table) q l (stretch b.σ (l+1)) ord}
    (chart : AdvisedBranch common) [Fact common.p.Prime] [Algebra (ZMod common.p) chart.E]
    (reader : ChosenReader chart (b.physical.teamsPred (l+1)+1) (stretch b.ρ (l+1))
      (b.physical.multBits (l+1)) (b.physical.tally (l+1)) (b.physical.word (l+1))
      (adv (adviceScale b.σ b.ρ (l+1))+6))
    (chargeFit : reader.charge ≤ c*(adv (adviceScale b.σ b.ρ (l+1))+1)^charge)



local notation "copies₁" => TeamScales.width (l+1) scales.α

open RoutingISA.Evaluator RoutingISA.CompactMachine TeamSite
open ResidueIndex ResidueBox
attribute [local irreducible] Nat.clog UniversalMachine.programPrefix
local notation3 (prettyPrint := false) "ColumnIndex" => Index (Fin (Module.finrank (ZMod common.p) chart.E))
  (Fin (pairedTableParameters (l+1) (size₁))) (chart.pinRadius (R₁+1) r₁)

local notation3 (prettyPrint := false) "W₁" => cal.frozenWitness
local notation3 (prettyPrint := false) "plan₁" => cal.seed.choose
local notation3 (prettyPrint := false) "sites₁" => (Fintype.equivFin (((W₁).routedFine position).Site)).toEmbedding
local notation3 (prettyPrint := false) "edges₁" => (Fintype.equivFin (((W₁).routedFine position).Edge)).toEmbedding
local notation3 (prettyPrint := false) "ports₁" => (Fintype.equivFin (Fin r₁ × Fin (publicWidth tape₁))).toEmbedding
local notation3 (prettyPrint := false) "number₁" => Fintype.equivFin (Cube D → Deck (EnrichedOuter.depth S (d₁+1) (epochs scales.τ (l+1))+1))
local notation3 (prettyPrint := false) "selectedSites" => cal.frozenSites grid qpos position chart reader chargeFit
local notation3 (prettyPrint := false) "task₁" => cal.frozenTask grid qpos position chart reader chargeFit
local notation3 (prettyPrint := false) "tag₁" => ParseTable.signedLiteralCode (s:=size₁) ord
local notation3 (prettyPrint := false) "P₁" => (signedProgram (cube.cubeID paid)).program
local notation3 (prettyPrint := false) "free₁" => (selectedSites).enrichedFree prog₁ P₁ (l+1) ec₁ ℓ₁
local notation3 (prettyPrint := false) "x₁" => fun _ : Unit => false
local notation3 (prettyPrint := false) "geoSeed" => ((plan₁).execute tape₁ order₁ position Unit).choose
local notation3 (prettyPrint := false) "mac₁" => TeamSiteEvents.macros (w:=w₁) (siteLibrary SparseExterior.driver) (nativeClock (l+1))

set_option cleanup.letToHave false in
/-- Read the native run on the original selected public history and number its
terms using the same enriched network and canonical pin bank as the realization. -/
noncomputable def SignedCalendarAt.frozenEnrichedRunAt
    (values : (seedBundle (tape₁) axes d₁ (order₁) position copies₁).Tables F)
    (h : ColumnIndex) :=
  let bounds := cal.frozenSpliceBounds grid
  let leaf := (plan₁).frozenLeaf tape₁ order₁ position W₁ tag₁ sites₁ edges₁ ports₁ values x₁
  @SeedPlan.selectedRunAsEnriched D «m» _ F K _ _ paid S
    R₁ r₁ (budget₁+6) ℓ₁ l d₁ extra₁ 64 w₁ ec₁ (w₁+1) size₁ copies₁ (epochs scales.τ (l+1)) header Q
    plan₁ cube φ ord q common chart prog₁ (geo₁).fits order₁ W₁ position
    (Fintype.card (((W₁).routedFine position).Site)) (Fintype.card (((W₁).routedFine position).Edge))
    (Fintype.card (Fin r₁ × Fin (publicWidth tape₁))) sites₁ edges₁ ports₁
    values ((geoSeed).eval x₁) leaf.property free₁ grid.count bounds.2.1 scales.α ξ₁ bounds.1
    (geo₁).literalSize bounds.2.2
    (Fintype.card (Cube D → Deck (EnrichedOuter.depth S (d₁+1) (epochs scales.τ (l+1))+1))) number₁
    (task₁).p.privateGap _ _ (b.physical.multBits (l+1)) w₁ reader
    (cal.frozenIssuedAddresses grid qpos position chart reader chargeFit) mac₁
    (selectedSites).publicWords (selectedSites).registers (selectedSites).limit.val (selectedSites).burst.val h

universe ui ux ua ub

/-- Assemble a fixed family after numbering each of its original executed columns. -/
private def realizeConvertedColumns {I : Sort ui} {X : Sort ux} {A : I → Sort ua} {B : I → Sort ub}
    (finish : ((j : I) → B j) → X) (numbered : (j : I) → A j → B j) (runs : (j : I) → A j) : X :=
  finish (fun j => numbered j (runs j))

set_option cleanup.letToHave false in
/-- A complete execution of every original residue pin on this selected site
yields a realization with the calendar's actual link, edge type and clocks. -/
noncomputable def SignedCalendarAt.realizeIssuedFrozenSites
    (values : (seedBundle (tape₁) axes d₁ (order₁) position copies₁).Tables F) :=
  @realizeConvertedColumns ColumnIndex _ _ _
    (@SignedCalendarAt.realizeFrozenSites D «m» _ F K _ _ paid S cube extra E p Q breadth sourcePower
      scales b φ q hm header C A₀ a B₀ b₀ J j coeff addr power cut adv c charge factor l
      cal grid qpos position ord common chart _ _ reader chargeFit values)
    (@SignedCalendarAt.frozenEnrichedRunAt D «m» _ F K _ _ paid S cube extra E p Q breadth sourcePower
      scales b φ q hm header C A₀ a B₀ b₀ J j coeff addr power cut adv c charge factor l
      cal grid qpos position ord common chart _ _ reader chargeFit values)

end Diagonal

end BorderVNP
end Computability
end OAI

import OAI.Computability.BorderVNP.DiagonalCalendarPlannerReportCoordinates

/-! # The registered owner of the original resident demand rows -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.RoutingOutputs.NativeDemands

open Crossing _root_.OAI.Computability.BorderVNP.Cube _root_.OAI.Computability.BorderVNP.Cube.Physical

variable {D C ne np n d blocks K h R b s : ℕ} {P : Type} [Fintype P] {bits : P → ℕ}
    {N : Network D P bits} {cell : N.Site → Fin C} {edge : N.Edge ↪ Fin ne} {port : P ↪ Fin np}
    {dir : Directory.Layout} {old : Fin dir.entries ↪ N.Site} {live : (Fin dir.teams × Fin dir.sites) ↪ P}
    {gap : ℕ} {bounds : dir.DestinationBounds} {positive : 0 < d}

local notation "sourceRows" => rows N cell edge port dir old live gap
set_option quotPrecheck false in
local notation "widths" => fun i : Fin (sourceRows).length => (sourceRows)[i.val].width
local notation "recvAt(" limit ")" => receiver N cell edge port dir old live gap limit
local notation "resident" => meanPackedLabel N cell (recvAt(bounds)) widths (List.finRange C) n d positive

private theorem ownerOnResidentRows {label plannedLabel : Fin C → Label (n+1) d}
    {plannedRecv : Fin (sourceRows).length → Fin C} {plannedWidth : Fin (sourceRows).length → ℕ}
    {owner : (Packet n d blocks → Selector n K h) → Fin d → Fin (R+1)}
    (prior : owner = greedyOwner R b s plannedLabel plannedRecv plannedWidth)
    (coordinates : label=plannedLabel ∧ recvAt(bounds)=plannedRecv ∧ widths=plannedWidth)
    (named : ∀ limit : dir.DestinationBounds, label=meanPackedLabel N cell (recvAt(limit)) widths (List.finRange C) n d positive) :
    owner=greedyOwner R b s resident (recvAt(bounds)) widths ∧ label=resident := by
  have atResident := named bounds
  refine ⟨?_,atResident⟩
  rw [←atResident,coordinates.1,coordinates.2.1,coordinates.2.2]
  exact prior

end Packing.RoutingOutputs.NativeDemands

namespace Diagonal

open Diagonal.ExternalSew Cover Packing Packing.DeckGrid Crossing Branch Epoch PackedHistoryCircuit
open PackedHistoryCircuit.Normalized SelectedSchedule EnrichedOuter TeamScales TeamContraction ProcessorSlots
open VPVNP ParseBatch ParseBatchVerifier Prewire VPVNP.ParseGrammar
open FieldProcessor RoutingISA RoutingISA.Evaluator RoutingISA.Transmission
open GeometryAdvice GeometryFrameEncoding RoutingISA.Pins VPVNP.BurstRAM RoutingISA.CompactMachine TeamSite
open DiagonalResidueRAM ResidueEntryInput ResidueRates ResiduePins
open Diagonal.ExternalSew GridHosts
open scoped Classical BorderVNP.Epoch.Cube

open Packing.Inherited Packing.Inherited.FrozenTape Shortening.PublicCapacity BorderVNP.Epoch.Round
open ResidueIndex ResidueBox
attribute [local instance] portFintype
attribute [local irreducible] Nat.clog UniversalMachine.programPrefix logWidth prefixCapacity
  FieldProcessor.freeWidth Fintype.equivFin
set_option maxRecDepth 8200
set_option maxHeartbeats 4400000
set_option synthInstance.maxSize 4000

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

variable {ord : Fin (l+1) × Bool ≃ Fin (2*(l+1))}
    {common : CommonField paid (φ ∘ cube.table) q l (stretch b.σ (l+1)) ord}
    (chart : AdvisedBranch common) [Fact common.p.Prime] [Algebra (ZMod common.p) chart.E]
    (reader : ChosenReader chart (b.physical.teamsPred (l+1)+1) (stretch b.ρ (l+1))
      (b.physical.multBits (l+1)) (b.physical.tally (l+1)) (b.physical.word (l+1))
      (adv (adviceScale b.σ b.ρ (l+1))+6))
    (chargeFit : reader.charge ≤ c*(adv (adviceScale b.σ b.ρ (l+1))+1)^charge)

local notation3 (prettyPrint := false) "plan₁" => cal.seed.choose
local notation3 (prettyPrint := false) "W₁" => cal.frozenWitness
local notation3 (prettyPrint := false) "sites₁" => (Fintype.equivFin (((W₁).routedFine position).Site)).toEmbedding
local notation3 (prettyPrint := false) "edges₁" => (Fintype.equivFin (((W₁).routedFine position).Edge)).toEmbedding
local notation3 (prettyPrint := false) "ports₁" => (Fintype.equivFin (Fin (r₁) × Fin (publicWidth (tape₁)))).toEmbedding
local notation3 (prettyPrint := false) "number₁" => Fintype.equivFin (Cube D → Deck (EnrichedOuter.depth S (d₁+1) T₁+1))
local notation3 (prettyPrint := false) "tag₁" => ParseTable.signedLiteralCode (s:=size₁) ord
local notation3 (prettyPrint := false) "x₁" => fun _ : Unit => false

local notation3 (prettyPrint := false) "matrices" => (seedBundle (tape₁) axes d₁ (order₁) position copies₁).Tables F
local notation3 (prettyPrint := false) "leafAt(" vs ")" => (plan₁).frozenLeaf tape₁ order₁ position W₁ tag₁ sites₁ edges₁ ports₁ vs x₁
local notation3 (prettyPrint := false) "histAt(" vs ")" => (packHistory (leafAt(vs)) (plan₁).compiled.machine.epoch T₁).Index

private def ownerStatement {p : Prop} (proof : p) : PSigma fun p : Prop => p := ⟨p,proof⟩

set_option cleanup.letToHave false in
set_option maxRecDepth 18000 in
set_option maxHeartbeats 15000000 in
private noncomputable def residentCoordinates (values : matrices) (hist : histAt(values)) :
    PSigma fun p : Prop => p :=
  let prior := cal.frozenSites_plannerMeanOwner grid qpos position chart reader chargeFit values hist
  let coords := cal.frozenPlannerReportCoordinates grid qpos position chart reader chargeFit values hist
  let packet := cal.frozenWriter_packetLabel grid qpos position chart reader chargeFit values hist
  ownerStatement <| RoutingOutputs.NativeDemands.ownerOnResidentRows prior coords packet

/-- The checked route and the original packet use the resident mean on the
uncast demand-row table, with exactly its original receiver and incoming width. -/
theorem SignedCalendarAt.frozenRegisteredResidentCoordinates (values : matrices) (hist : histAt(values)) :
    (residentCoordinates cal grid qpos position chart reader chargeFit values hist).1 :=
  (residentCoordinates cal grid qpos position chart reader chargeFit values hist).2

/-- The registered owner in the resident report's original geometry. -/
theorem SignedCalendarAt.frozenRegisteredResidentOwner (values : matrices) (hist : histAt(values)) :
    type_of% ((cal.frozenRegisteredResidentCoordinates grid qpos position chart reader chargeFit values hist).1) :=
  (cal.frozenRegisteredResidentCoordinates grid qpos position chart reader chargeFit values hist).1

end Diagonal

end BorderVNP
end Computability
end OAI

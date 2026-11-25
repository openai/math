import OAI.Computability.BorderVNP.DiagonalCalendarWriterTopology
import OAI.Computability.BorderVNP.DiagonalCalendarPreparedPacket
import OAI.Computability.BorderVNP.DiagonalCalendarPlannerTask

/-! # Native chart and address fields of the frozen report planner -/

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

variable (grid : LocatedSignedGridAt cube b header (l+1))
    (qpos : 1 ≤ Q)
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


open Packing.RoutingOutputs CellMacro.Generator

open Packing.CellAddresses Packing.CellAddressCircuit Packing.CellAddressPhysical

private theorem networkAtLayout {ar br : CubeArena.Layout} {D s n d k b J A : ℕ}
    {P σ : Type} [Fintype P] [Fintype σ] {bits : P → ℕ} {N : Network D P bits}
    {cell : N.Site → Fin ar.cells} {aux : N.Site → ℕ} {siteID : N.Site ↪ Fin s}
    {edgeID : N.Edge ↪ Fin ar.cables} {portID : P ↪ Fin n}
    {F : Fields s ar.cables n ar.cells d k b σ} {x : σ → Bool}
    {old : Fin J → Fin s} {ports : Fin A → Fin n} {origin : ℕ} {ram : ℕ → ℕ}
    (same : ar=br) (net : Represents N cell aux siteID edgeID portID F x)
    (ids : ∀ c, (F.cells c).val=c.val)
    (width : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c<2^b)
    (image : Image F old ports x origin ram) :
    let idx := cast (congrArg (fun a : CubeArena.Layout => N.Site → Fin a.cells) same) cell
    let eid := cast (congrArg (fun a : CubeArena.Layout => N.Edge ↪ Fin a.cables) same) edgeID
    let fields := cast (congrArg (fun a : CubeArena.Layout => Fields s a.cables n a.cells d k b σ) same) F
    Represents N idx aux siteID eid portID fields x ∧ (∀ c, (fields.cells c).val=c.val) ∧
      (∀ c, guessedSize N idx c+siteSize N idx c aux+suppliedSize N idx c<2^b) ∧
      Image fields old ports x origin ram := by
  cases same
  exact ⟨net,ids,width,image⟩

set_option maxHeartbeats 16000000 in
/-- A complete frozen packet realizes the original network in the calibrated planner layout.
All identifiers, per-cell width bounds and RAM addresses use that same layout. -/
noncomputable def SignedCalendarAt.plannerNetworkOnPacket
    (values : (seedBundle (tape₁) axes d₁ (order₁) position copies₁).Tables F)
    :=
  let topology := cal.frozenWriterTopology grid qpos position chart reader chargeFit values
  let same := congrArg SignedTaskArena.Layout.cube (cal.frozenPlannerTask_eq grid qpos position chart reader chargeFit)
  PLift.up <| fun hist ram (packet : cal.frozenPacketImage grid qpos position chart reader chargeFit values hist ram) =>
    let net := (topology hist).down
    networkAtLayout same net.1 (fun _ => rfl) net.2 packet.1

end Diagonal

end BorderVNP
end Computability
end OAI

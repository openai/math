import OAI.Computability.BorderVNP.DiagonalCandidatePlannerReturnTerm
import OAI.Computability.BorderVNP.DiagonalCalendarPlannerTask
import OAI.Computability.BorderVNP.DiagonalCalendarCandidateSites

/-! # The returned native candidate on the report planner’s cube -/

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
local notation "cap₁" => SeedPlan.profileReserve (r₁) (l+1)

open Packing.Inherited Packing.Inherited.FrozenTape Shortening.PublicCapacity BorderVNP.Epoch.Round Cover
open EnrichedOuter

attribute [local instance] portFintype
local notation3 (prettyPrint := false) "plan₁" => cal.seed.choose

variable {ord : Fin (l+1) × Bool ≃ Fin (2*(l+1))}
    {common : CommonField paid (φ ∘ cube.table) q l (stretch b.σ (l+1)) ord}
    (chart : AdvisedBranch common) [Fact common.p.Prime] [Algebra (ZMod common.p) chart.E]
    (reader : ChosenReader chart (b.physical.teamsPred (l+1)+1) (stretch b.ρ (l+1))
      (b.physical.multBits (l+1)) (b.physical.tally (l+1)) (b.physical.word (l+1))
      (adv (adviceScale b.σ b.ρ (l+1))+6))
    (chargeFit : reader.charge ≤ c*(adv (adviceScale b.σ b.ρ (l+1))+1)^charge)

local notation3 (prettyPrint := false) "layout₁" => cal.frozenLayout chart reader chargeFit

local notation3 (prettyPrint := false) "names₁" => (cal.frozenWitness).routedFine position
local notation3 (prettyPrint := false) "sites₁" => (Fintype.equivFin (names₁).Site).toEmbedding
local notation3 (prettyPrint := false) "edges₁" => (Fintype.equivFin (names₁).Edge).toEmbedding
local notation3 (prettyPrint := false) "ports₁" => (Fintype.equivFin (Fin (r₁) × Fin (publicWidth (tape₁)))).toEmbedding
local notation3 (prettyPrint := false) "tag₁" => ParseTable.signedLiteralCode (s:=size₁) ord
local notation3 (prettyPrint := false) "x₁" => fun _ : Unit => false
local notation3 (prettyPrint := false) "widths₁" => fun i => Fintype.card (Machine.Guess S (d₁+1)
  (fun _ _ => 60*logWidth (r₁) (l+1)) i)
local notation3 (prettyPrint := false) "slots₁" => fun i => Fintype.equivFin (Machine.Guess S (d₁+1)
  (fun _ _ => 60*logWidth (r₁) (l+1)) i)
local notation3 (prettyPrint := false) "fit₁" => (plan₁).profile_order_fits widths₁ slots₁
local notation3 (prettyPrint := false) "seed₁" v => (plan₁).frozenLeaf (tape₁) (order₁) position cal.frozenWitness tag₁
  sites₁ edges₁ ports₁ v x₁
local notation3 (prettyPrint := false) "geoSeed" => ((plan₁).execute (tape₁) (order₁) position Unit).choose
local notation3 (prettyPrint := false) "code₁" v => (plan₁).compiled.machine.nativeCode (seed₁ v) geoSeed x₁ rfl widths₁ slots₁ fit₁

local notation3 (prettyPrint := false) "selectedTask" => cal.frozenTask grid qpos position chart reader chargeFit

open CellMacro.Generator RoutingISA.CompactMachine

local notation3 (prettyPrint := false) "headers₁" => JointHeader.PositiveFields cap₁ (selectedTask).cube.n
  (selectedTask).cube.header.d (selectedTask).cube.header.cap (R₁+1) (selectedTask).dim (b.physical.tally (l+1))
open Packing.CellAddresses Packing.RoutingOutputs Packing.CellAddressPhysical
open ExternalSew.RowTrace ExternalSew.FieldExport GridHosts Packing.DeckGrid
open CellEntries JointHeader Routing

open Packing.RoutingOutputs Packing.CellAddresses TeamContraction.JointHeader CompactMachine
open _root_.OAI.Computability.BorderVNP.Cube Cube.Physical Cube.Tally Cube.LabelIndex

private def receivedPlannerEvidence {claim : Prop} (given : claim) : PSigma (fun p : Prop => p) :=
  ⟨claim,given⟩

set_option cleanup.letToHave false in
set_option maxHeartbeats 32000000 in
private noncomputable def SignedCalendarAt.plannerEvidenceForSite
    (routing : LocatedFrozenRoutingAt cube b φ q adv c charge (l+1))
    (values : (seedBundle tape₁ axes d₁ order₁ position copies₁).Tables F)
    (h : (packHistory (seed₁ values) (plan₁).compiled.machine.epoch T₁).Index)
    (p : headers₁) (encoded : ((code₁ values) h).val=p.profile)
    (fixed : Routing.Block (R₁+1)) (pin : Fin pins₁ → Bool) (wire : HeaderExterior layout₁ p.bits) :=
  let same := cal.frozenPlannerTask_eq grid qpos position chart reader chargeFit
  let returned := cal.frozenSites_header_boot grid qpos position chart reader chargeFit fixed pin p wire
  let roster := cal.frozenSites_boots grid qpos position chart reader chargeFit fixed
  let node := roster.2.choose pin ⟨wire.val,returned.choose⟩
  fun (u : Fin (R₁+1)) (g : Fin (node u).start.guessWidth → Bool) (valid : RoutingISA.LocalRow.declarationInRange p.cube) allowed =>
    let original := cal.frozenCandidateSites grid qpos position chart reader chargeFit routing values h p encoded
      fixed pin wire u g valid allowed
    @receivedPlannerEvidence _ (returnedSiteAtPlanner% original.down (node u).installed_routines_at
      (congrArg SignedTaskArena.Layout.cube same))

set_option cleanup.letToHave false in
set_option maxHeartbeats 32000000 in
/-- The very same physical return, read at the equal cube layout used by the
report planner. Both the native site and its recorded RAM refer to this pin. -/
noncomputable def SignedCalendarAt.frozenPlannerCandidateSites
    (routing : LocatedFrozenRoutingAt cube b φ q adv c charge (l+1))
    (values : (seedBundle tape₁ axes d₁ order₁ position copies₁).Tables F)
    (h : (packHistory (seed₁ values) (plan₁).compiled.machine.epoch T₁).Index)
    (p : headers₁) (encoded : ((code₁ values) h).val=p.profile)
    (fixed : Routing.Block (R₁+1)) (pin : Fin pins₁ → Bool) (wire : HeaderExterior layout₁ p.bits) :=
  fun u g valid allowed =>
    let observed := cal.plannerEvidenceForSite grid qpos position chart reader chargeFit routing values h p encoded
      fixed pin wire u g valid allowed
    @PLift.up observed.1 observed.2

end Diagonal

end BorderVNP
end Computability
end OAI

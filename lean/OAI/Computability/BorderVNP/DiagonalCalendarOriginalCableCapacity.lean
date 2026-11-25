import OAI.Computability.BorderVNP.DiagonalCalendarWriterTopology
import OAI.Computability.BorderVNP.DiagonalCalendarMeanPairCapacity
import OAI.Computability.BorderVNP.DiagonalCalendarPlannerTask
import OAI.Computability.BorderVNP.DiagonalFrozenExecutionRange
import OAI.Computability.BorderVNP.DiagonalCalendarRoutedInputs

/-! # The capacity of the original calendar cables on the installed packet layout -/

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

variable (oper : FrozenExecutionAt cube b φ q adv c charge header (hm:=hm) (l+1))
local notation "grid" => oper.grid
variable (qpos : 1 ≤ Q)
    (position : (Fin (Fintype.card (Cube D)) → Deck (CoverScale.initialDepth (Cube D)
      (stretch b.ρ (l+1)) (l+1)-1+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
local notation "T₁" => epochs scales.τ (l+1)
local notation "copies₁" => TeamScales.width (l+1) scales.α
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

local notation3 (prettyPrint := false) "physical₁" => cal.frozenSites grid qpos position chart reader chargeFit
local notation3 (prettyPrint := false) "program₁" => (withStartup (signedBody (cube.cubeID paid))).program
local notation3 (prettyPrint := false) "wired₁" => wiringWith (prog₁) (program₁) physical₁ (pins₁) (ℓ₁) (l+1) ec₁ (geo₁).fits
local notation3 (prettyPrint := false) "names₁" => (cal.frozenWitness).routedFine position
local notation3 (prettyPrint := false) "sites₁" => (Fintype.equivFin (names₁).Site).toEmbedding
local notation3 (prettyPrint := false) "edges₁" => (Fintype.equivFin (names₁).Edge).toEmbedding
local notation3 (prettyPrint := false) "ports₁" => (Fintype.equivFin (Fin (r₁) × Fin (publicWidth (tape₁)))).toEmbedding
local notation3 (prettyPrint := false) "tag₁" => ParseTable.signedLiteralCode (s:=size₁) ord
local notation3 (prettyPrint := false) "x₁" => fun _ : Unit => false
local notation3 (prettyPrint := false) "seed₁" v => (plan₁).frozenLeaf (tape₁) (order₁) position cal.frozenWitness tag₁
  sites₁ edges₁ ports₁ v x₁

open CellMacro.Generator RoutingISA.CompactMachine

open Packing.CellAddresses Packing.RoutingOutputs Packing.CellAddressPhysical
open ExternalSew.RowTrace ExternalSew.FieldExport GridHosts Packing.DeckGrid
open CellEntries JointHeader Routing

local notation3 (prettyPrint := false) "owners₁" => Fintype.equivFin (Cube D → Deck (EnrichedOuter.depth S (d₁+1) T₁+1))
local notation3 (prettyPrint := false) "free₁" => (physical₁).enrichedFree prog₁ program₁ (l+1) ec₁ ℓ₁
local notation3 (prettyPrint := false) "netAt[" v "," h "]" =>
  EnrichedTape.network (pins:=pins₁) prog₁ (geo₁).fits position free₁ (oper.grid).count
    (plan₁).compiled.machine (seed₁ v) rfl h
local notation3 (prettyPrint := false) "stageAt[" v "," h "]" => ((packHistory (seed₁ v) (plan₁).compiled.machine.epoch T₁).term h).val
local notation3 (prettyPrint := false) "cellsAt[" v "," h "]" => fun site : (netAt[v,h]).Site =>
  owners₁ (reduceMove (EnrichedOuter.depth S (d₁+1) T₁) ((stageAt[v,h]).route.origin site))
local notation3 (prettyPrint := false) "params₁" => (⟨R₁,r₁,(wired₁).program.length+(cutWidth (l+1)+extra₁),ℓ₁,
  GridHosts.inputBlockWidth r₁ (l+1) axes d₁,tiles⟩ : FieldExport.Params)
local notation3 (prettyPrint := false) "valid₁" => (⟨(oper.grid).block_pos,(oper.grid).block_le.trans_eq (oper.grid).link_eq,
  gridRoom wired₁ Fintype.card_pos⟩ : (params₁).Valid)
local notation3 (prettyPrint := false) "edgesAt[" v "," h "]" => mergedEdges params₁ valid₁ ((stageAt[v,h]).rows.edge)
local notation3 (prettyPrint := false) "portsAt" => (finProdFinEquiv : FreeBlock R₁ tiles ≃ Fin ((R₁+1)*tiles)).toEmbedding
open RoutingISA.Evaluator.ScheduleClock
open TeamContraction.JointHeader

local notation3 (prettyPrint := false) "planner" => cal.frozenPlannerTask grid qpos position chart reader chargeFit

open _root_.OAI.Computability.BorderVNP.Cube _root_.OAI.Computability.BorderVNP.Cube.Physical _root_.OAI.Computability.BorderVNP.Cube.MeanChoice _root_.OAI.Computability.BorderVNP.Cube.LabelIndex

attribute [local irreducible] stretch Nat.clog logWidth prefixCapacity Fintype.equivFin
  UniversalMachine.programPrefix FieldProcessor.freeWidth
set_option maxRecDepth 14000
set_option maxHeartbeats 16000000
set_option cleanup.letToHave false

private def capacityReceipt {P : Prop} (h : P) : PSigma fun q : Prop => q := ⟨P,h⟩

private noncomputable def actualCableCapacity
    (values : (seedBundle tape₁ axes d₁ order₁ position copies₁).Tables F)
    (hist : (packHistory (seed₁ values) (plan₁).compiled.machine.epoch T₁).Index) : PSigma fun q : Prop => q :=
  let ord₀ := NativeDemands.cableOrder (netAt[values,hist]) (cellsAt[values,hist]) (edgesAt[values,hist])
  capacityReceipt <| cal.frozenSites_meanPairCapacityForOrder grid position values hist
    free₁ (planner).p.privateGap ord₀

/-- The sum of the crossing cable widths at each ordered pair of actual cell
labels fits the installed packet blocks. The network, field bits, row sizes,
private gap and cable numbering are those used by this calendar. -/
theorem SignedCalendarAt.originalArgumentPairBound
    (values : (seedBundle tape₁ axes d₁ order₁ position copies₁).Tables F)
    (hist : (packHistory (seed₁ values) (plan₁).compiled.machine.epoch T₁).Index) :
    (actualCableCapacity cal oper qpos position chart reader chargeFit values hist).1 :=
  (actualCableCapacity cal oper qpos position chart reader chargeFit values hist).2

end Diagonal

end BorderVNP
end Computability
end OAI

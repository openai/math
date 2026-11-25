import OAI.Computability.BorderVNP.DiagonalCalendarPlannerTask
import OAI.Computability.BorderVNP.DiagonalCalendarBoxHeaderRoom
import OAI.Computability.BorderVNP.DiagonalCalendarOriginalSiteRoom
import OAI.Computability.BorderVNP.DiagonalCalendarOriginalPrograms
import OAI.Computability.BorderVNP.DiagonalCalendarPlacementExtents
import OAI.Computability.BorderVNP.PackedReportPrivateSlotBound

/-! # The original report slots and bodies throughout a frozen layout -/

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
set_option maxHeartbeats 1300000

variable {D m : ℕ} [NeZero D] {F K : Type} [Field F] [Field K] {paid : PaidIdentity F D m}
    {schedule₀ : PackedHistoryCircuit.Normalized.SiteSchedule paid} {cube : FixedCube K} {extra E p Q breadth sourcePower : ℕ}
    {scales : EpochScales schedule₀ (cube.pred+1) extra}
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
local notation "J₁" => (EnrichedOuter.fan (e:=paid) schedule₀)^T₁*tiles
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
local notation3 (prettyPrint := false) "task₁" => cal.frozenTask grid qpos position chart reader chargeFit

open GeometryAdviceRate TeamContraction.JointHeader Cube.Physical Packing.BottomReports DiagonalTallyCellReports
open CellEntries Shortening Shortening.Adaptive BorderVNP.Epoch.Round Diagonal.ExternalSew.RowTrace
attribute [local instance] portFintype

local notation3 (prettyPrint := false) "blank" => TimedProcessor.scaleData (signedProgram (cube.cubeID paid)).program
  (siteLibrary SparseExterior.driver) (fun _ : Fin 8 => some false) (geo₁) (fun _ _ => 0) (fun _ _ => 0)
  (fun _ _ => false) (fun _ _ _ => false)
local notation3 (prettyPrint := false) "P₁" => (withStartup (signedBody (cube.cubeID paid))).program
local notation3 (prettyPrint := false) "nameSite" => (Fintype.equivFin (cal.frozenWitness.routedFine position).Site).toEmbedding
local notation3 (prettyPrint := false) "nameEdge" => (Fintype.equivFin (cal.frozenWitness.routedFine position).Edge).toEmbedding
local notation3 (prettyPrint := false) "namePort" => (Fintype.equivFin (Fin (r₁) × Fin (publicWidth (tape₁)))).toEmbedding
local notation3 (prettyPrint := false) "data₁" => cal.frozenSites grid qpos position chart reader chargeFit
local notation3 (prettyPrint := false) "t₁" => (located₁).raw.reserve ceiling₁
local notation3 (prettyPrint := false) "external₁" => TeamScales.exterior (ξ₁) (r₁) (l+1)
local notation3 (prettyPrint := false) "wired₁" => wiringWith (prog₁) (P₁) (data₁) (pins₁) (ℓ₁) (l+1) (ec₁) (geo₁).fits

local notation3 (prettyPrint := false) "tag" => ParseTable.signedLiteralCode (s:=size₁) ord
local notation3 (prettyPrint := false) "channels" => (groupedGridRows (tape₁) axes d₁ (order₁) position copies₁).edge
local notation3 (prettyPrint := false) "groups" => (Equiv.refl (Fin tiles)).toEmbedding
local notation3 (prettyPrint := false) "orderJ" => finProdFinEquiv.symm.trans
  ((Equiv.refl (Fin ((EnrichedOuter.fan (e:=paid) schedule₀)^T₁))).prodCongr (order₁))
local notation3 (prettyPrint := false) "origin₁" => Allocation.dest
  ((initial₁).next+7*(dir₁).candidates) cap₁ (t₁).size (located₁).outputs w₁
local notation3 (prettyPrint := false) "control₁" => RoutingOutputs.controlsBase (origin₁)
  (task₁).cube.cables (task₁).cube.cells (dir₁).entries ((dir₁).teams*(dir₁).sites)
local notation3 (prettyPrint := false) "report₁" => DiagonalTallyAllocation.reportLayout (task₁).before (task₁).after
  (initial₁).frame (control₁) (task₁).p.parameters (task₁).p.siteWidth (task₁).p.bodyCap (task₁).cube.stop

local notation3 (prettyPrint := false) "sourceBundle" => cal.frozenWitness.retainedBundle
  (copies:=copies₁) position (orderJ) tag nameSite nameEdge namePort channels groups

local notation3 (prettyPrint := false) "plan₁" => cal.seed.choose
local notation3 (prettyPrint := false) "x₁" => fun _ : Unit => false
local notation3 (prettyPrint := false) "seed₁[" v "]" => (plan₁).frozenLeaf (tape₁) (order₁) position
  cal.frozenWitness tag nameSite nameEdge namePort v x₁
local notation3 (prettyPrint := false) "owners₁" => Fintype.equivFin (Cube D → Deck (EnrichedOuter.depth schedule₀ (d₁+1) T₁+1))
local notation3 (prettyPrint := false) "free₁" => (data₁).enrichedFree (prog₁) (P₁) (l+1) ec₁ ℓ₁
local notation3 (prettyPrint := false) "netAt[" v "," h "]" =>
  EnrichedTape.network (pins:=pins₁) (prog₁) (geo₁).fits position free₁ grid.count
    (plan₁).compiled.machine (seed₁[v]) rfl h
local notation3 (prettyPrint := false) "stageAt[" v "," h "]" => ((packHistory (seed₁[v]) (plan₁).compiled.machine.epoch T₁).term h).val
local notation3 (prettyPrint := false) "cellsAt[" v "," h "]" => fun site : (netAt[v,h]).Site =>
  owners₁ (reduceMove (EnrichedOuter.depth schedule₀ (d₁+1) T₁) ((stageAt[v,h]).route.origin site))
local notation3 (prettyPrint := false) "hostsAt[" v "," h "]" =>
  originalDescriptionRows (plan₁).compiled.machine (seed₁[v]) h dir₁ rfl (order₁)


open Packing.CellAddresses Packing.CellAddressCircuit Packing.CellAddressPhysical Packing.RoutingOutputs


local notation3 (prettyPrint := false) "valid₁" =>
  (⟨grid.block_pos,grid.block_le.trans_eq grid.link_eq,GridHosts.gridRoom (wired₁) Fintype.card_pos⟩ :
    (fieldSewParams (wired₁) axes d₁).Valid)
open CellSparse.Packet.Source

local notation3 (prettyPrint := false) "originalBody" j =>
  cal.frozenWitness.seedStored position tag nameSite nameEdge namePort channels groups (orderJ j).2
local notation3 (prettyPrint := false) "privateOffset[" v "," h "," t "," j "]" =>
  (NativeDemands.destination (netAt[v,h]) (cellsAt[v,h])
    (FieldExport.mergedEdges (fieldSewParams (wired₁) axes d₁) valid₁ (stageAt[v,h]).rows.edge)
    (finProdFinEquiv : FreeBlock (R₁) tiles ≃ Fin ((R₁+1)*tiles)).toEmbedding
    dir₁ (hostsAt[v,h]) (Equiv.refl (FreeBlock (R₁) tiles)).toEmbedding (t).p.privateGap (.inl j)).2
local notation3 (prettyPrint := false) "slotAt[" v "," h "," t "," j "]" =>
  (t).cube.cellBank+((cellsAt[v,h]) ((hostsAt[v,h]) j)).val*(t).cube.cellStride+privateOffset[v,h,t,j]
local notation "hdr" => header*logWidth r₁ (l+1)

/-- A site slot can contain a complete original box whenever its relative
end fits the receiving stride. -/
private theorem withinCellStop {bank cell stride cells offset span : ℕ}
    (inside : offset+span ≤ stride) (valid : cell+1 ≤ cells) :
    bank ≤ bank+cell*stride+offset ∧
    bank+cell*stride+offset+span ≤ bank+cells*stride := by
  have room := Nat.mul_le_mul_right stride valid
  rw [Nat.succ_mul] at room
  omega

/-- Before any routes or reports are chosen, every actual original input
box lies in its receiving cell and its body fits the transmitted short header. -/
theorem SignedCalendarAt.frozenFundedBoxBounds [Fact (8≤header)]
    (values : (seedBundle tape₁ axes d₁ order₁ position copies₁).Tables F)
    (history : (packHistory (seed₁[values]) (plan₁).compiled.machine.epoch T₁).Index) :
    ∀ j : Fin J₁, ((task₁).cube.cellBank ≤ slotAt[values,history,task₁,j] ∧
      slotAt[values,history,task₁,j]+(dir₁).description ≤ (task₁).cube.stop) ∧
      hdr+(boxBody (originalBody j)).length ≤ (dir₁).description ∧
      (boxBody (originalBody j)).length < 2^hdr := by
  intro j
  let N := netAt[values,history]
  let cell := cellsAt[values,history]
  let host := hostsAt[values,history]
  let eid := FieldExport.mergedEdges (fieldSewParams (wired₁) axes d₁) valid₁ (stageAt[values,history]).rows.edge
  let pid := (finProdFinEquiv : FreeBlock R₁ tiles ≃ Fin ((R₁+1)*tiles)).toEmbedding
  let live := (Equiv.refl (FreeBlock R₁ tiles)).toEmbedding
  have cells : Fintype.card (Cube D → Deck (EnrichedOuter.depth schedule₀ (d₁+1) T₁+1))=(task₁).cube.cells := by
    change _ = CoverScale.sites (Cube D) (EnrichedOuter.depth schedule₀ (CoverScale.initialDepth (Cube D) r₁ (l+1)) T₁)
    rw [grid.depth_eq]
    rfl
  have span := cal.frozenSites_placement_extents grid qpos position chart reader chargeFit values history
  have ends := (NativeDemands.private_description_interval N cell eid pid dir₁ host live (task₁).p.privateGap j).2
  have paid := (span.2 (cell (host j))).2.trans_eq span.1.symm
  have room := cal.frozenSites_placed_siteRoom grid qpos position chart reader chargeFit (Fact.out (p:=8≤header))
    values history (fun _ _ => false) j
  have cap : (boxBody (originalBody j)).length ≤ (report₁).bodyCap := room.body
  have data := room.descriptionRoom
  have width := (cal.frozenSites_report_shape grid qpos position chart reader chargeFit).1
  have tail : (report₁).fieldWidth+(report₁).bodyCap ≤ (dir₁).description :=
    (Nat.le_add_right _ _).trans data
  have payload := (Nat.add_le_add_left cap (report₁).fieldWidth).trans tail
  have bodyFits : hdr+(boxBody (originalBody j)).length ≤ (dir₁).description := width ▸ payload
  exact ⟨withinCellStop (ends.trans paid) ((cell (host j)).isLt.trans_eq cells),bodyFits,
    (Nat.le_add_left _ _).trans_lt (bodyFits.trans_lt (cal.frozenDescription_headerRoom grid))⟩

local notation3 (prettyPrint := false) "planner" => cal.frozenPlannerTask grid qpos position chart reader chargeFit

/-- The same bounds at the exact planner addresses published in its original
slot table. The task transport preserves the complete source payload. -/
theorem SignedCalendarAt.frozenLookupOriginalArgumentRanges [Fact (8≤header)]
    (values : (seedBundle tape₁ axes d₁ order₁ position copies₁).Tables F)
    (history : (packHistory (seed₁[values]) (plan₁).compiled.machine.epoch T₁).Index) :
    ∀ j : Fin J₁, ((planner).cube.cellBank ≤ slotAt[values,history,planner,j] ∧
      slotAt[values,history,planner,j]+(dir₁).description ≤ (planner).cube.stop) ∧
      hdr+(boxBody (originalBody j)).length ≤ (dir₁).description ∧
      (boxBody (originalBody j)).length < 2^hdr := by
  have same : task₁=planner := (cal.frozenEarlyTask grid qpos position chart reader chargeFit).symm.trans
    (cal.frozenPlannerTask_eq grid qpos position chart reader chargeFit)
  rw [←same]
  exact cal.frozenFundedBoxBounds grid qpos position chart reader chargeFit values history

end Diagonal

end BorderVNP
end Computability
end OAI

import OAI.Computability.BorderVNP.DiagonalCalendarPlacementExtents
import OAI.Computability.BorderVNP.DiagonalCalendarFrontWindows
import OAI.Computability.BorderVNP.DiagonalCalendarControlFormats
import OAI.Computability.BorderVNP.PackedNativeDemandRows
import OAI.Computability.BorderVNP.PackedFrozenTapedInstallation
import OAI.Computability.BorderVNP.PackedTerminalSignedHosts

/-! # Native demand rows and both front windows of the issued calendar history -/

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
local notation3 (prettyPrint := false) "dir₁" => freeDirectory (R₁) (r₁)
  ((tape₁).program.length+(cutWidth (l+1)+extra₁)) (ℓ₁) tiles (GridHosts.inputBlockWidth (r₁) (l+1) axes (d₁)) J₁ description


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
local notation3 (prettyPrint := false) "blank₁" => TimedProcessor.scaleData (signedProgram (cube.cubeID paid)).program
  (siteLibrary SparseExterior.driver) (fun _ : Fin 8 => some false) (geo₁)
  (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => false) (fun _ _ _ => false)
local notation3 (prettyPrint := false) "forward₁" => wiringWith prog₁ program₁ blank₁ pins₁ ℓ₁ (l+1) ec₁ (geo₁).fits
local notation3 (prettyPrint := false) "names₁" => (cal.frozenWitness).routedFine position
local notation3 (prettyPrint := false) "sites₁" => (Fintype.equivFin (names₁).Site).toEmbedding
local notation3 (prettyPrint := false) "edges₁" => (Fintype.equivFin (names₁).Edge).toEmbedding
local notation3 (prettyPrint := false) "ports₁" => (Fintype.equivFin (Fin (r₁) × Fin (publicWidth (tape₁)))).toEmbedding
local notation3 (prettyPrint := false) "tag₁" => ParseTable.signedLiteralCode (s:=size₁) ord
local notation3 (prettyPrint := false) "x₁" => fun _ : Unit => false

local notation3 (prettyPrint := false) "seed₁[" v "]" => (plan₁).frozenLeaf (tape₁) (order₁) position
  cal.frozenWitness tag₁ sites₁ edges₁ ports₁ v x₁
local notation3 (prettyPrint := false) "owners₁" => Fintype.equivFin (Cube D → Deck (EnrichedOuter.depth S (d₁+1) T₁+1))
local notation3 (prettyPrint := false) "free₁" => (blank₁).enrichedFree (prog₁) (program₁) (l+1) ec₁ ℓ₁
local notation3 (prettyPrint := false) "task₁" => cal.frozenTask grid qpos position chart reader chargeFit
local notation3 (prettyPrint := false) "stageAt[" v "," h "]" => ((packHistory (seed₁[v]) (plan₁).compiled.machine.epoch T₁).term h).val
local notation3 (prettyPrint := false) "netAt[" v "," h "]" =>
  FieldExport.finalLayout (fieldSewParams forward₁ axes d₁)
    (GridHosts.attachedHosts forward₁ Fintype.card_pos grid.count (Shortening.Adaptive.flattenPack T₁ (stageAt[v,h]).pack).layout)
local notation3 (prettyPrint := false) "cellsAt[" v "," h "]" => fun site : (netAt[v,h]).Site =>
  owners₁ (reduceMove (EnrichedOuter.depth S (d₁+1) T₁) ((stageAt[v,h]).route.origin site))
local notation3 (prettyPrint := false) "hostsAt[" v "," h "]" =>
  originalDescriptionRows (plan₁).compiled.machine (seed₁[v]) h dir₁ rfl (order₁)

open Packing.RoutingOutputs RoutingISA.Evaluator.ScheduleClock

local notation3 (prettyPrint := false) "initial₁" => reader.startupArenaWith (n:=l+1) (reg:=64)
  (prog₁) (a₁) (ℓ₁) (cal.frozenLayout chart reader chargeFit).header
local notation3 (prettyPrint := false) "located₁" => cal.locatedGateTable grid qpos position (initial₁)
local notation "X₁" => TeamScales.exterior ξ₁ r₁ (l+1)
local notation "cap₁" => SeedPlan.profileReserve r₁ (l+1)
local notation "ceiling₁" => geometryGateCeiling (8*(11920000+1500000+16008100*coeff+37)) (4*(E+2)) r₁ (l+1)
local notation3 (prettyPrint := false) "fixed₁" => (CubeConstants.install (cube.cubeID paid)).slots
local notation "args₁" => _root_.OAI.Computability.BorderVNP.Cube.Tally.argumentWidth cube.pred cube.b cube.h cube.copies cube.width
local notation "finish₁" => cubeCoefficient cube.pred cube.b cube.h cube.copies cube.width args₁
local notation "read₁" => _root_.OAI.Computability.BorderVNP.Cube.TeamRowClock.physicalCoefficient cube.pred cube.b cube.h cube.copies cube.width

local notation "public₁" => ⌈publicWork (cube.pred+1) scales.α r₁ (l+1) (R₁+1)⌉₊
local notation "local₁" => ⌈localWork (cube.pred+1) (E+2) scales.α ξ₁ r₁ (l+1) (R₁+1)⌉₊
local notation "route₁" => 512*(cube.pred+1+_root_.OAI.Computability.BorderVNP.Cube.Tally.selectorWidth cube.pred cube.copies cube.h+1)

attribute [local irreducible] Nat.clog Fintype.card Finset.univ

set_option maxHeartbeats 3600000 in
/-- On the original issued history, the seven-word directory and its actual post-publication
layout determine the core and preparation charges on the chosen calendar. -/
theorem SignedCalendarAt.frozenSites_issued_front_window
    (front : LocatedTableFrontAt cube b (E+2) fixed₁ finish₁ read₁ (l+1))
    (routing : LocatedFrozenRoutingAt cube b φ q adv c charge (l+1))
    (values : (seedBundle (tape₁) axes d₁ (order₁) position copies₁).Tables F)
    (hist : (packHistory (seed₁[values]) (plan₁).compiled.machine.epoch T₁).Index) :
    let N := netAt[values,hist]
    let cell := cellsAt[values,hist]
    let old := hostsAt[values,hist]
    let dir := dir₁
    let task := task₁
    let ar := task.cube
    let tab := located₁
    let initial := initial₁
    let live := Function.Embedding.refl (Fin (R₁+1) × Fin tiles)
    let cost := uniformWindows r₁ (R₁+1) X₁ public₁ local₁ route₁ fixed₁ finish₁ read₁
    ∀ {ne np : ℕ} (edge : N.Edge ↪ Fin ne) (port : (Fin (R₁+1) × Fin tiles) ↪ Fin np)
      (axis : ℕ) (after : ℕ → ℕ),
      let layout := _root_.OAI.Computability.BorderVNP.Cube.LabelIndex.layout initial.frame after
      let rows := NativeDemands.rows N cell edge port dir old live task.p.privateGap
      layout.cells=ar.cells → layout.cableCount=ar.cables → layout.deliveryCount=rows.length → layout.labels=ar.alphabet →
      2048*(X₁+(R₁+1+1)^3+(rows.length+ar.header.d.choose 2)+r₁+1)≤cost.core ∧
        GeometryAdviceRate.ticks (tab.raw.reserve ceiling₁).size cap₁ tab.outputs w₁ w₁+
          beforeDirectory (R₁+1) dir.sites dir.entries+
          rawScheduleTicks ar initial.frame initial.broadcastBase axis R₁ rows.length after≤cost.before := by
  intro N cell old dir task ar tab initial live cost ne np edge port axis after layout rows hc he hr hl
  let pp := NativeDemands.privatePair N cell edge port dir old live task.p.privateGap
  let lp := NativeDemands.livePair N cell edge port dir old live task.p.privateGap
  have bound := cal.frozenSites_front_windows grid qpos position chart reader chargeFit (E+2) fixed₁ finish₁ read₁
    front routing pp lp axis after hc he hr hl
  have selected : scales.signedWindows (E+2) route₁ fixed₁ finish₁ read₁ (l+1) r₁ = cost := by
    dsimp only [cost,EpochScales.signedWindows]
    rw [(b.sizes (Nat.succ_pos l)).1]
  rw [←selected]
  exact bound

set_option maxHeartbeats 3600000 in
/-- The same physical stride bounds each cell's private tail and the global original-row
scan. The live and private pair addresses used by the scan fit the hardware word. -/
theorem SignedCalendarAt.frozenSites_issued_placement_bounds
    (routing : LocatedFrozenRoutingAt cube b φ q adv c charge (l+1))
    (values : (seedBundle (tape₁) axes d₁ (order₁) position copies₁).Tables F)
    (hist : (packHistory (seed₁[values]) (plan₁).compiled.machine.epoch T₁).Index) :
    let N := netAt[values,hist]
    let cell := cellsAt[values,hist]
    let old := hostsAt[values,hist]
    let dir := dir₁
    let task := task₁
    let ar := task.cube
    let tab := located₁
    let initial := initial₁
    let origin := Allocation.dest (initial.next+7*dir.candidates) cap₁ ceiling₁ tab.outputs w₁
    let pl := privateLayout initial.frame origin ar.cables ar.cells dir.entries dir.description task.p.privateGap
    let ports := bases origin ar.cables ar.cells dir.entries
    (∀ c, Packing.CellAddresses.suppliedSize N cell c+task.p.privateGap+
      (∑ j, if cell (old j)=c then dir.description else 0)≤ar.cellStride) ∧
      (∀ c, Packing.CellAddresses.suppliedSize N cell c+task.p.privateGap+dir.entries*dir.description≤ar.cellStride) ∧
      controlsBase origin ar.cables ar.cells dir.entries (dir.teams*dir.sites)+8<2^w₁ ∧
      Directory.ISA.wordBound (Directory.ISA.placementBound dir pl.raw ports.livePairs ar.cellStride)<2^w₁ := by
  intro N cell old dir task ar tab initial origin pl ports
  have loads : (plan₁).SewnCellLoads grid.count ℓ₁ := by rw [←grid.link_eq]; exact grid.cellLoads _ _
  have installed := ((plan₁).frozen_leaf_installed tape₁ order₁ position cal.frozenWitness tag₁ sites₁ edges₁ ports₁ values x₁).trans
    (SewnTape.native_grid_installed order₁ position prog₁ program₁ blank₁ (geo₁).fits)
  have aligned := enrichedBlockHosts_attached forward₁ axes d₁ order₁ position grid.count (plan₁).compiled.machine (seed₁[values]) installed hist
  have prepared := (plan₁).frozen_signed_placement_extents prog₁ (geo₁).fits cal.frozenWitness position tag₁
    sites₁ edges₁ ports₁ values x₁ free₁ grid.count loads hist owners₁ old
    (fun n small => grid.placementSpan ((l+1)^2) n le_rfl small)
  have cells (c) : (Packing.CellAddresses.suppliedSize N cell c+task.p.privateGap+
      (∑ j, if cell (old j)=c then dir.description else 0)≤ar.cellStride) ∧
      Packing.CellAddresses.suppliedSize N cell c+task.p.privateGap+dir.entries*dir.description≤ar.cellStride := by
    dsimp only [N]
    rw [aligned]
    exact prepared c
  obtain ⟨_,_,ctl,words,_⟩ := cal.locatedGateTable_routing grid qpos position chart reader chargeFit routing
  have headerFit : ar.header.header<2^w₁ := (cal.frozenControlFormats grid qpos position chart reader chargeFit).2.2.1
  rw [tab.reserved_size] at ctl words
  refine ⟨fun c => (cells c).1,fun c => (cells c).2,?_,words⟩
  have fields : controlsBase origin ar.cables ar.cells dir.entries (dir.teams*dir.sites)+37≤ar.header.header := ctl
  omega

end Diagonal

end BorderVNP
end Computability
end OAI

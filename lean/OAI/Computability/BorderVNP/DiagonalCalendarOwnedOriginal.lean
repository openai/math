import OAI.Computability.BorderVNP.DiagonalOriginalReportDelivery
import OAI.Computability.BorderVNP.DiagonalCalendarOriginalSiteRoom
import OAI.Computability.BorderVNP.DiagonalCalendarOriginalPrograms
import OAI.Computability.BorderVNP.DiagonalCalendarPlacementExtents
import OAI.Computability.BorderVNP.PackedReportPrivateSlotBound

/-! # All original marked reports at the selected calendar's owned host return -/

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
set_option maxHeartbeats 3000000 in
/-- The complete original-report input for a team's owned host scatter at the selected
calendar. Its receiving addresses and private accounting are computed on the same named
terminal as the installed geometry, including all field factors, fine uses and sidecars.
Applying `OriginalReportDelivery.hostImage` gives the membership-indexed delivered and
site-room callback for any actual owned and published control entry on this execution. -/
theorem SignedCalendarAt.frozenSites_owned_original
    (headerWide : 8 ≤ header)
    (values : (seedBundle (tape₁) axes d₁ (order₁) position copies₁).Tables F)
    (history : (packHistory (seed₁[values]) (plan₁).compiled.machine.epoch T₁).Index)
    (later : Routing.WireLayout (R₁+1) (r₁) (ℓ₁)) (same : (layout₁).header=later.header)
    (pin : Fin pins₁ → Bool) (wire : Exterior (R₁) (r₁) (ℓ₁) → Bool) :
    let N := netAt[values,history]
    let cell := cellsAt[values,history]
    let host := hostsAt[values,history]
    let dir := dir₁
    let live := (Equiv.refl (FreeBlock (R₁) tiles)).toEmbedding
    let eid := FieldExport.mergedEdges (fieldSewParams (wired₁) axes d₁) valid₁ (stageAt[values,history]).rows.edge
    let pid := (finProdFinEquiv : FreeBlock (R₁) tiles ≃ Fin ((R₁+1)*tiles)).toEmbedding
    let sid := (stageAt[values,history]).rows.site
    let states := cal.frozenSitesOriginalPrograms grid qpos position chart reader chargeFit values history
    let aux := fun site : N.Site => (states site).program.size
    let absolute := fun i : Fin J₁ => (task₁).cube.cellBank+(cell (host i)).val*(task₁).cube.cellStride+
      (NativeDemands.destination N cell eid pid dir host live (task₁).p.privateGap (.inl i)).2
    let boxBase := fun i : Fin J₁ => siteBase N cell (cell (host i)) sid aux ⟨host i,rfl⟩
    let cells := Fintype.card (Cube D → Deck (EnrichedOuter.depth schedule₀ (d₁+1) T₁+1))
    let sites := (boundaryShape schedule₀ (d₁+1) T₁).sites
    let cables := (boundaryShape schedule₀ (d₁+1) T₁).edges+(fieldSewParams (wired₁) axes d₁).slots
    ∀ {levels keyWidth : ℕ} {σ : Type} [Fintype σ]
      (F₂ : Fields sites cables ((R₁+1)*tiles) cells levels keyWidth (w₁) σ) (x : σ → Bool)
      (before placed : ℕ → ℕ) (owner : ℕ → Fin (R₁+1)) (runs : Fin (R₁+1) → TeamHistory (w₁))
      (ib hb sb : Fin (R₁+1) → ℕ),
      let tables := bases origin₁ cables cells dir.entries
      let pl := privateLayout (initial₁).frame origin₁ cables cells dir.entries dir.description (task₁).p.privateGap
      let pp := Directory.ISA.placement placed tables.privatePairs
      let lp := Directory.ISA.placement placed tables.livePairs
      Represents N cell aux sid eid pid F₂ x → (∀ c, (F₂.cells c).val=c.val) →
      Image F₂ (sid ∘ host) (pid ∘ live ∘ finProdFinEquiv.symm) x origin₁ before →
      pl.Image before dir.entries placed → pl.Fits (w₁) before →
      ReturnedDelivery (wired₁) pin wire later dir pp lp owner (task₁).cube.cellBank (task₁).cube.cellStride runs
        (fun u => Wiring.pinLayout (wired₁) u (ib u) (hb u) (sb u)) →
      ∀ bank : Fin J₁ → ℕ → Bool, OriginalReportDelivery (task₁) dir N cell host owner (fun u => (runs u).history.val.2.2)
        report₁ (sourceBundle absolute boxBase bank) := by
  intro N cell host dir live eid pid sid states aux absolute boxBase cells sites cables levels keyWidth σ _
    F₂ x before placed owner runs ib hb sb tables pl pp lp rep ids image placement placeFit returning bank
  have fit := cal.frozenSites_original_addressFit grid qpos position chart reader chargeFit values history
  have span := cal.frozenSites_placement_extents grid qpos position chart reader chargeFit values history
  have globalRoom (c : Fin cells) : suppliedSize N cell c+(task₁).p.privateGap+dir.entries*dir.description ≤ (task₁).cube.cellStride :=
    (span.2 c).2.trans_eq span.1.symm
  have cellCount : cells=(task₁).cube.cells := by
    change Fintype.card (Cube D → Deck (EnrichedOuter.depth schedule₀ (d₁+1) T₁+1)) =
      CoverScale.sites (Cube D) (EnrichedOuter.depth schedule₀ (CoverScale.initialDepth (Cube D) r₁ (l+1)) T₁)
    rw [grid.depth_eq]
    rfl
  refine ⟨cellCount,?_,?_,?_,?_,?_⟩
  · exact cal.frozenSites_placed_original grid qpos position chart reader chargeFit values history later same pin wire
      aux sid eid pid F₂ x before placed owner runs ib hb sb rep ids fit image placement placeFit returning bank
  · intro c
    have enough := globalRoom c
    omega
  · intro j
    have bound := (NativeDemands.private_description_interval N cell eid pid dir host live (task₁).p.privateGap j).1
    change _ ≤ absolute j
    dsimp only [absolute]
    exact Nat.add_le_add_left ((Nat.le_add_right ..).trans bound) _
  · intro j
    have bound := (NativeDemands.private_description_interval N cell eid pid dir host live (task₁).p.privateGap j).2
    change absolute j+dir.description ≤ _
    dsimp only [absolute]
    rw [Nat.add_assoc]
    exact Nat.add_le_add_left (bound.trans (globalRoom _)) _
  · exact cal.frozenSites_placed_siteRoom grid qpos position chart reader chargeFit headerWide values history bank

end Diagonal

end BorderVNP
end Computability
end OAI

import OAI.Computability.BorderVNP.DiagonalCalendarEarlyParameters
import OAI.Computability.BorderVNP.DiagonalCalendarPlacementExtents
import OAI.Computability.BorderVNP.DiagonalCalendarPublicationRoom
import OAI.Computability.BorderVNP.PackedFrozenDirectoryPublication

/-! # Address and cell capacity bounds for the rebuilt signed publisher -/

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


local notation3 (prettyPrint := false) "layout₁" => cal.frozenLayout chart reader chargeFit
local notation3 (prettyPrint := false) "initial₁" => reader.startupArenaWith (n:=l+1) (reg:=64)
  (prog₁) (a₁) (ℓ₁) (layout₁).header
local notation3 (prettyPrint := false) "located₁" => cal.locatedGateTable grid qpos position (initial₁)

local notation3 (prettyPrint := false) "physical₁" => cal.frozenSites grid qpos position chart reader chargeFit
local notation3 (prettyPrint := false) "program₁" => (withStartup (signedBody (cube.cubeID paid))).program
local notation3 (prettyPrint := false) "wired₁" => wiringWith (prog₁) (program₁) physical₁ (pins₁) (ℓ₁) (l+1) ec₁ (geo₁).fits
local notation3 (prettyPrint := false) "names₁" => (cal.frozenWitness).routedFine position
local notation3 (prettyPrint := false) "sites₁" => (Fintype.equivFin (names₁).Site).toEmbedding
local notation3 (prettyPrint := false) "edges₁" => (Fintype.equivFin (names₁).Edge).toEmbedding
local notation3 (prettyPrint := false) "ports₁" => (Fintype.equivFin (Fin (r₁) × Fin (publicWidth (tape₁)))).toEmbedding
local notation3 (prettyPrint := false) "tag₁" => ParseTable.signedLiteralCode (s:=size₁) ord
local notation3 (prettyPrint := false) "x₁" => fun _ : Unit => false

local notation3 (prettyPrint := false) "seed₁[" v "]" => (plan₁).frozenLeaf (tape₁) (order₁) position
  cal.frozenWitness tag₁ sites₁ edges₁ ports₁ v x₁
local notation3 (prettyPrint := false) "owners₁" => Fintype.equivFin (Cube D → Deck (EnrichedOuter.depth S (d₁+1) T₁+1))
local notation3 (prettyPrint := false) "free₁" => (physical₁).enrichedFree (prog₁) (program₁) (l+1) ec₁ ℓ₁
local notation3 (prettyPrint := false) "task₁" => cal.frozenTask grid qpos position chart reader chargeFit
local notation3 (prettyPrint := false) "netAt[" v "," h "]" =>
  EnrichedTape.network (pins:=pins₁) (prog₁) (geo₁).fits position free₁ grid.count
    (plan₁).compiled.machine (seed₁[v]) rfl h
local notation3 (prettyPrint := false) "stageAt[" v "," h "]" => ((packHistory (seed₁[v]) (plan₁).compiled.machine.epoch T₁).term h).val
local notation3 (prettyPrint := false) "cellsAt[" v "," h "]" => fun site : (netAt[v,h]).Site =>
  owners₁ (reduceMove (EnrichedOuter.depth S (d₁+1) T₁) ((stageAt[v,h]).route.origin site))
local notation3 (prettyPrint := false) "hostsAt[" v "," h "]" =>
  originalDescriptionRows (plan₁).compiled.machine (seed₁[v]) h dir₁ rfl (order₁)


open Packing.RoutingOutputs

/-- Bounds consumed by the private placement and seven-column publication
on a particular geometry array and a particular startup directory. -/
structure SignedPublicationSpace (a : StartupArena) (t : SignedTaskArena.Layout) (dir : Directory.Layout)
    (origin bufferExtent width : ℕ) : Prop where
  stop : t.cube.stop < 2^width
  cells : t.cube.cells ≤ 2^width
  span : a.next+7*dir.candidates ≤ origin
  rawRoom : a.next+7*dir.candidates ≤ t.cube.header.header
  ctl : controlsBase origin t.cube.cables t.cube.cells dir.entries (dir.teams*dir.sites)+8 < 2^width
  wordRoom : let loc := privateLayout a.frame origin t.cube.cables t.cube.cells dir.entries dir.description t.p.privateGap
    let tbl := bases origin t.cube.cables t.cube.cells dir.entries
    Directory.ISA.wordBound (Directory.ISA.placementBound dir loc.raw tbl.livePairs bufferExtent) < 2^width
  stride : t.cube.cellStride=bufferExtent

private theorem publicationSpaceOfRouting (a : StartupArena) (t : SignedTaskArena.Layout) (d : Directory.Layout)
    (origin budget width : ℕ) {tail : Prop}
    (bounds : budget<2^width ∧ t.cube.stop<2^width ∧ t.cube.cells≤2^width ∧
      a.next+7*d.candidates≤origin ∧ a.next+7*d.candidates≤t.cube.header.header ∧
      controlsBase origin t.cube.cables t.cube.cells d.entries (d.teams*d.sites)+8<2^width ∧ tail)
    (word : let ptr := bases origin t.cube.cables t.cube.cells d.entries
      Directory.ISA.wordBound (Directory.ISA.placementBound d ptr.privatePairs ptr.livePairs t.cube.cellStride)<2^width) :
    SignedPublicationSpace a t d origin t.cube.cellStride width :=
  ⟨bounds.2.1,bounds.2.2.1,bounds.2.2.2.1,bounds.2.2.2.2.1,bounds.2.2.2.2.2.1,word,rfl⟩

local notation "cap₁" => SeedPlan.profileReserve (r₁) (l+1)
local notation "ceiling₁" => geometryGateCeiling (8*(11920000+1500000+16008100*coeff+37)) (4*(E+2)) (r₁) (l+1)
local notation3 (prettyPrint := false) "nativeDir" => freeDirectory R₁ r₁
  ((wired₁).program.length+(cutWidth (l+1)+extra₁)) ℓ₁ tiles (GridHosts.inputBlockWidth r₁ (l+1) axes d₁) J₁ description
local notation3 (prettyPrint := false) "packetDir" => freeDirectory R₁ r₁ (initial₁).literal ℓ₁ tiles
  (GridHosts.inputBlockWidth r₁ (l+1) axes d₁) J₁ description
local notation3 (prettyPrint := false) "outputBase" =>
  Allocation.dest ((initial₁).next+7*(packetDir).candidates) cap₁ ((located₁).raw.reserve ceiling₁).size (located₁).outputs w₁
local notation3 (prettyPrint := false) "actual" => task₁
local notation3 (prettyPrint := false) "rebuilt" => (actual).withNetwork
  (Fintype.card (Cube D → Deck (EnrichedOuter.depth S (d₁+1) T₁+1)))
  ((boundaryShape S (d₁+1) T₁).edges+4*(R₁+1)*tiles)

set_option maxHeartbeats 3500000 in
/-- The public table uses the destination computed from the packet's literal
width. Its placement loops run on the directory whose literal width is read
from the deployed wiring. Both name the same allocated rows. -/
theorem SignedCalendarAt.frozenSites_publish_space (routing : LocatedFrozenRoutingAt cube b φ q adv c charge (l+1)) :
    SignedPublicationSpace initial₁ rebuilt nativeDir outputBase (actual).cube.cellStride w₁ := by
  let dest (d : Directory.Layout) := Allocation.dest ((initial₁).next+7*d.candidates) cap₁
    ((located₁).raw.reserve ceiling₁).size (located₁).outputs w₁
  let space (z : SignedTaskArena.Layout × Directory.Layout × Directory.Layout) :=
    SignedPublicationSpace initial₁ z.1 z.2.1 (dest z.2.2) (actual).cube.cellStride w₁
  have bound := cal.frozenPublicationRoom grid qpos position chart reader chargeFit routing
  have address := (cal.locatedGateTable_routing grid qpos position chart reader chargeFit routing).2.2.2.1
  have fitted : space (actual,cal.frozenDirectory,cal.frozenDirectory) :=
    publicationSpaceOfRouting initial₁ actual cal.frozenDirectory (dest cal.frozenDirectory)
      (TeamScales.exterior (ξ₁) (r₁) (l+1)) w₁ bound address
  have early := cal.frozenEarlyTask grid qpos position chart reader chargeFit
  have wired : nativeDir=cal.frozenDirectory := rfl
  have packet : packetDir=cal.frozenDirectory := (cal.frozenSourceRoom grid qpos position chart reader chargeFit).1
  have coordinates : ((rebuilt,nativeDir,packetDir) : SignedTaskArena.Layout × Directory.Layout × Directory.Layout) =
      (actual,cal.frozenDirectory,cal.frozenDirectory) :=
    Prod.ext early (Prod.ext wired packet)
  exact (congrArg space coordinates).mpr fitted

local notation3 (prettyPrint := false) "original[" v "," h "]" =>
  originalDescriptionRows (plan₁).compiled.machine (seed₁[v]) h nativeDir rfl (order₁)

set_option maxHeartbeats 3500000 in
/-- For the row numbering of this same native directory, each cell's own
published records fit the rebuilt task. The global scan fits the stride
from the actual selected task at every cell. -/
theorem SignedCalendarAt.frozenSites_publish_cells
    (values : (seedBundle (tape₁) axes d₁ (order₁) position copies₁).Tables F)
    (history : (packHistory (seed₁[values]) (plan₁).compiled.machine.epoch T₁).Index) :
    ∀ c, (Packing.CellAddresses.suppliedSize (netAt[values,history]) (cellsAt[values,history]) c+
      (actual).p.privateGap+(∑ j : Fin J₁,
        if (cellsAt[values,history]) ((original[values,history]) j)=c then description else 0)
        ≤ (rebuilt).cube.cellStride) ∧
      Packing.CellAddresses.suppliedSize (netAt[values,history]) (cellsAt[values,history]) c+
        (actual).p.privateGap+J₁*description ≤ (actual).cube.cellStride := by
  have bounds := cal.frozenSites_placement_extents grid qpos position chart reader chargeFit values history
  have stride := congrArg (fun t : SignedTaskArena.Layout => t.cube.cellStride)
    (cal.frozenEarlyTask grid qpos position chart reader chargeFit)
  intro c
  exact ⟨(bounds.2 c).1.trans_eq stride.symm,(bounds.2 c).2.trans_eq bounds.1.symm⟩

end Diagonal

end BorderVNP
end Computability
end OAI

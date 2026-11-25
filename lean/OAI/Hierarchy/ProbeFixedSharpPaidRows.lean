import OAI.Hierarchy.ProbeFixedWidePrintedPairCap
import OAI.Hierarchy.ProbeFixedWideForestAperture
import OAI.Hierarchy.ProbeFixedWideSpillCases
import OAI.Hierarchy.ProbeFixedWideRetainedPrefix
import OAI.Hierarchy.ProbePaidEventBounds
import OAI.Hierarchy.TaggedWideWorkspaceTariff

namespace OAI
/-! # Native paid width per physical edge and calendar event -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires StockCommit
open scoped Classical Fin.CommRing

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
set_option quotPrecheck false
local notation "P" => v.widePlacement h width
local notation "s" => v.nativeBoards P h width
local notation "A" => v.privateArena P h width
local notation "D" => 2^v.W
local notation "N" => Stages h D
local notation "r" => Fintype.card (Slots h D k)
local notation "w" => Native.wordBits h D Native.copies
local notation "start" => v.catalystStaticStart P h width
local notation "cnt" => rowOnlyCount v.mesh (declaredRows v.mesh (ownerLedger s v.mesh (P).catalogue (P).routes F A))
local notation "stock" => v.fixedTerminalStock P h width
local notation "page" => v.wideSignedPage h width stock
local notation "banks" => TerminalLayout.settlement page stock
local notation "src" => TerminalLayout.source page
local notation "tab" => TerminalLayout.table page
local notation "dst" => TerminalLayout.destination page
local notation "owners" => sinkBank start cnt r (P).catalogue.rows
local notation "order" => wideRouteOrder h D k
local notation "directory" => WideMemory.dir h v.W k v.wideJobs
local notation "route" => CoreRoute.source v.sampler h v.W k v.wideJobs v.depth (WideMemory.K h v.W)
  (directory).groups (WideMemory.H h v.W k v.wideJobs) (WideMemory.R v.sampler h v.W k)
local notation "C" => v.wideSignedChart h width stock


local notation "f" => v.nativeFormats P h width
local notation "lay" => FeedLayout.atEvent («N»:=N) v.mesh A f (P).joint.initial width v.keepLimit
local notation "sink" => (P).catalogue.sink r banks src tab dst owners
local notation "coreSpill" => v.paidSpillPath P h width (routeBanks start cnt r) route order
local notation "feedSpill" => v.paidFeedPath P h width route lay

/-- The public event tariff includes the two original direct sockets, selector
tree and escaping stock routes, along with each boundary feed lane. -/
def sharpPaidUnit :=
  v.wideUnitCost v.paidRoleRate v.forestFactor
    (max (v.overflowFactor v.menu.maximum) (v.overflowFactor (v.keepLimit+1)))

set_option maxHeartbeats 2000000 in
theorem wide_sharp_paid_rows :
    ∀ᶠ h : ℕ in Filter.atTop, ∀ width, width≤2^h → v.widthFloor≤width →
      v.keepLimit*width+1≤2^h →
      let placed:=v.widePlacement h width
      let arena:=v.privateArena placed h width
      let funds:=v.fixedTerminalStock placed h width
      let ordering:=wideRouteOrder h (2^v.W) k
      ∀ size,arena.endAddress v.mesh≤ size→∀ (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W)),
      let final:=v.wideSignedCheckoutAt h width size funds v.radius π ordering raw
      final (arena.endAddress v.mesh)=0→∀ ev∈events v.mesh,∀e : Fin placed.catalogue.rows,
        PaidWidths.total (v.wideEventSlices h width v.maxBits ev) final e≤v.sharpPaidUnit*width := by
  filter_upwards [v.wide_printed_pair_cap,v.wide_forest_aperture,v.wide_paid_spill_cases] with h pairs forest spill
  intro width small floor budget placed arena funds ordering size extent π raw final accepted ev present e
  have spillRows:=spill width small floor budget size extent π raw accepted
  let formatsAt := v.nativeFormats placed h width
  let wireDirectory := WideMemory.dir h v.W k v.wideJobs
  let wireSource := CoreRoute.source v.sampler h v.W k v.wideJobs v.depth (WideMemory.K h v.W)
    wireDirectory.groups (WideMemory.H h v.W k v.wideJobs) (WideMemory.R v.sampler h v.W k)
  cases ev with
  | attempt a =>
    have pair:=(pairs width small budget size extent π raw a present e).2
    have tree:=(forest width small budget size extent π raw a present e).2
    let direct:=v.paidRoleRate
    let branch:=v.overflowFactor v.menu.maximum
    have unit : 2*direct+v.forestFactor+branch≤v.sharpPaidUnit := by
      unfold sharpPaidUnit wideUnitCost
      exact (Nat.add_le_add_left (le_max_left _ _) _).trans (le_max_left _ _)
    have bill : 2*(direct*width)+v.forestFactor*width+branch*width≤v.sharpPaidUnit*width := by
      calc
        _=(2*direct+v.forestFactor+branch)*width := by ring
        _≤_ := Nat.mul_le_mul_right width unit
    let boardsAt := v.nativeBoards placed h width
    let slotCount := Fintype.card (Slots h (2^v.W) k)
    let rowCount := rowOnlyCount v.mesh (declaredRows v.mesh
      (ownerLedger boardsAt v.mesh placed.catalogue placed.routes F arena))
    let staticStart := v.catalystStaticStart placed h width
    let signedPage := v.wideSignedPage h width funds
    let rowSink := placed.catalogue.sink slotCount (TerminalLayout.settlement signedPage funds)
      (TerminalLayout.source signedPage) (TerminalLayout.table signedPage) (TerminalLayout.destination signedPage)
      (sinkBank staticStart rowCount slotCount placed.catalogue.rows)
    let spillPath := v.paidSpillPath placed h width (routeBanks staticStart rowCount slotCount) wireSource ordering
    exact (formatsAt a).per_row_bound rowSink placed.catalogue.idBase
      (StripChart.header F boardsAt a).fieldTerm (StripChart.id F boardsAt placed.catalogue a)
      (v.nativeTrees placed h width a) (spillPath a) v.maxBits final e (direct*width) (v.forestFactor*width)
      (branch*width) (v.sharpPaidUnit*width) pair.direct pair.mate tree (spillRows.1 a present e) bill
  | feed b =>
    let feed:=v.overflowFactor (v.keepLimit+1)
    let stageCount := Stages h (2^v.W)
    let feedLayoutAt := FeedLayout.atEvent («N»:=stageCount) v.mesh arena formatsAt placed.joint.initial width v.keepLimit
    let feedPath := v.paidFeedPath placed h width wireSource feedLayoutAt
    have unit : FeedLayout.lanes stageCount k*feed≤v.sharpPaidUnit := by
      rw [show stageCount=publicStages v.W from fixed_stage_count h v.W]
      unfold sharpPaidUnit wideUnitCost
      exact (Nat.mul_le_mul_left _ (le_max_right _ _)).trans (le_max_right _ _)
    have bill:=boundary_per_row (feedLayoutAt b) (feedPath b) final (feed*width) e
      (fun z hz=>spillRows.2 b present z hz e)
    change PaidWidths.total (v.wideEventSlices h width v.maxBits (.feed b)) final e ≤
      FeedLayout.lanes stageCount k*(feed*width) at bill
    rw [← Nat.mul_assoc] at bill
    exact bill.trans (Nat.mul_le_mul_right width unit)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI

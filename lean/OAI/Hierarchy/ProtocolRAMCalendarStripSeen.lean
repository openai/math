import OAI.Hierarchy.ProtocolRAMCalendarStripArena
import OAI.Hierarchy.ProtocolRAMCalendarRemainders
import OAI.Hierarchy.ProtocolRAMCalendarFeedLifetime
import OAI.Hierarchy.ProtocolRAMCatalogueRows

namespace OAI
/-! # Observing every original site receipt after the real calendar has finished -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.StripChart.Slab
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native PurchaseFrozen PurchaseStage
open StripDirectory
open scoped Classical Fin.CommRing
variable {z d k q depth r : ℕ}
local notation "stageCount" => List.length (Fabric.shapes (permutationFabric z d))
local notation "W" => wordBits z d copies

variable (v : Slab) (s : Boards z d k q depth) (F : Type*) [Field F]
  [SiteNaming (ColumnSite (PayloadStrip.Columns (List.length (Fabric.shapes (permutationFabric z d)))) k)] [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)]
  (c : Mesh) (initial width cap : ℕ) (finish : ℝ) (prices : PhasePrice) (catalogue : CatalogueRows.Board)
  (banks : RouteSettlement.Banks) (src tbl dst : ℕ) (owners : Bank)
local notation "A" => arena v s
local notation "B" => install v s c
local notation "S" => catalogue.sink r banks src tbl dst owners
local notation "C" => chart F c A initial width cap B finish prices catalogue r banks src tbl dst owners
local notation "f" => formats F c A initial B

/-- A word in the current priced commit's slab is below the first writable
address of every later chronological step. -/
theorem final_cell (mem current : Memory W) (a : Attempt) {prior tail : List Event}
    (cut : Slot C mem (.attempt a) prior tail current) (x : ℕ) (low : x<(f a).pricedArea.stop) :
    run C (events c) mem x=after C (.attempt a) current x := by
  apply cut.word
  intro t member
  have later := cut.later t member
  have next := (A).apart c later
  have bound := fit v s F c initial a
  exact (priced_event_floor_for (N:=stageCount) c finish prices A f initial width cap S catalogue.idBase
    (fun a=>(header F B a).fieldTerm) (id F B catalogue) (order v s F c initial) t x
    (low.trans_le (bound.trans next))).1

theorem verdict_before {z d k q n : ℕ} (g : Format z d k q n) :
    g.board.verdict<g.pricedArea.stop := by
  simp only [Format.pricedArea,Format.area,Format.labelStart,StockCommit.Area.stop,
    StockCommit.Area.output,StockCommit.Area.excess,StockCommit.Area.clip,
    StockCommit.Area.src,StockCommit.Area.broadcast,StockCommit.Area.direct]
  omega

/-- The output byte matches the selected row's original code, live bit, payload,
or captured price, even after subsequent accepted or rejected trials. -/
theorem final_column (mem current : Memory W) (a : Attempt) {prior tail : List Event}
    (cut : Slot C mem (.attempt a) prior tail current)
    (physical : Board ((C).layout a) (repair C a) W) (p : Pass) (hp : p∈writes ((C).layout a) (repair C a))
    (i : Fin p.rows) :
    run C (events c) mem (p.out+i.val)=p.term.eval
      (postSnapshot ((C).layout a) (repair C a) (prepared C a current)) (i.val:Word W) := by
  have before := physical.flagAfter p hp
  have high := verdict_before (f a)
  have contained : p.out+i.val<(f a).pricedArea.stop := by
    change p.out+p.rows≤(f a).board.verdict at before
    have := i.isLt
    omega
  exact (final_cell v s F c initial width cap finish prices catalogue banks src tbl dst owners
    mem current a cut _ contained).trans (attempt_read C a current cut.currentReady physical p hp i)

/-- Acceptance for the historic choice is read from that slot's terminal flag,
including malformed raw private words. -/
theorem final_verdict (mem current : Memory W) (a : Attempt) {prior tail : List Event}
    (cut : Slot C mem (.attempt a) prior tail current) :
    run C (events c) mem (repair C a).verdict=0 ↔ accepted C (.attempt a) current := by
  have low : (repair C a).verdict < (f a).pricedArea.stop := verdict_before (f a)
  rw [final_cell v s F c initial width cap finish prices catalogue banks src tbl dst owners
    mem current a cut (repair C a).verdict low]
  exact attempt_verdict C a current cut.currentReady

end Hierarchy.ProtocolRAM.Calendar.StripChart.Slab
end

end OAI

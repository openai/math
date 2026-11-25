import OAI.Hierarchy.ProbeFixedSpillPlacement
import OAI.Hierarchy.ProbeFixedRepairSlot
import OAI.Hierarchy.ProbeFixedFailureCeilings
import OAI.Hierarchy.ProbeFixedThresholdAdmission
import OAI.Hierarchy.ProbeFixedMountedRowRead
import OAI.Hierarchy.ProbeFixedPurchasedPopulation
import OAI.Hierarchy.ProbeFixedPurchasedArchiveBuffers
import OAI.Hierarchy.ProbeFixedRowGeometry
import OAI.Hierarchy.ProbeFixedSelectedRepair

namespace OAI
/-! # Physical paid-repair rows from the original payload and purchased attempts -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe AdaptiveProbe.OuterBank ProbeStage ProbeStage.Native CoreBoard StripChart
open StockCommit PurchaseStage RepairHistogram CatalystArchive StripDirectory PurchaseFrozen CatalogueRows
open scoped BigOperators Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} [Nonempty (Fin k)] {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width r : ℕ)
  (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "W" => wordBits z (2^v.W) copies
local notation "N" => Stages z (2^v.W)
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "A" => v.billedAccount P z width r banks src tab dst owners
local notation "bs" => v.nativeBoards P z width
local notation "H" => v.publicHeader P z width
local notation "f" => v.nativeFormats P z width
local notation "bills" => v.issued P z width r banks src tab dst owners
local notation "FEE" => charges F (v.sized (v.seed P z width) width) v.cost (H).stop
local notation "arena" => v.privateArena P z width

section
set_option maxRecDepth 4096
variable (phase trial : ℕ) (entry : Memory (wordBits z (2^v.W) copies))
local notation "ev" => Attempt.outer phase trial
local notation "pre" => (guard C ev).apply entry
local notation "checked" => postSnapshot ((C).layout ev) (repair C ev) (prepared C ev entry)
local notation "stage" => v.stage P z width r banks src tab dst owners ev entry
local notation "t" => Calendar.time v.mesh v.finish ev
variable (fitted : v.payloadStageSizes P z width r banks src tab dst owners phase trial entry)
local notation "x" => v.payloadStageInput P z width r banks src tab dst owners phase trial entry fitted
local notation "π" => v.payloadStage_compile P z width r banks src tab dst owners phase trial entry fitted
variable (s : v.RepairSlot P z width r banks src tab dst owners (.outer phase trial) entry)
local notation "live" => s.slot.currentReady
local notation "T" => v.selectedTape P z width r banks src tab dst owners ev entry s.layout live π
local notation "test" => v.payloadTest P z width phase trial

set_option maxHeartbeats 2000000 in
include fitted s in
def payload_repair (geom : v.PayloadRepairGeometry P z width r banks src tab dst owners phase trial entry)
    (maxWord : (H).payload.maxWord<2^W)
    : (A).bank.FailedRows (2^z) width v.actualK v.keepLimit v.loss v.menu.margin t
      ((A).read (Succession v.mesh (.attempt ev)).1 entry)
      ((A).read (Succession v.mesh (.attempt ev)).2 (after C (.attempt ev) entry)) := by
  classical
  have wordPositive : 0<W := by unfold wordBits; omega
  have date:=dateInTable_of_event v.mesh ev s.event
  have timeMin : (v.finish:ℝ)/2≤t := by
    have positive : 0<(v.finish:ℝ):=by exact_mod_cast v.clock.finish_pos
    exact (show (v.finish:ℝ)/2≤v.finish by linarith).trans (v.real_times date).1
  have positive : 0<t := (half_pos (show 0<(v.finish:ℝ) by exact_mod_cast v.clock.finish_pos)).trans_le timeMin
  have pages:=s.pages
  have room:=v.purchased_table_room z s.late
  have saved:=v.row_buffer_stock P z width r banks src tab dst owners ev entry live bills
  have first:=v.row_quote_cells P z width bills ev entry pre date pages.guard.header.scalar pages.guard.scores
    room.2.2.2 (fun i=>(saved i).1) s.limit
  have inspected:=v.row_quote_cells P z width bills ev entry checked date pages.checked.header.scalar pages.checked.scores
    room.2.2.2 (fun i=>(saved i).2.1) s.limit
  have last:=v.row_quote_cells P z width bills ev entry stage date pages.stage.header.scalar pages.stage.scores
    room.2.2.2 (fun i=>(saved i).2.2) s.limit
  have eligible:=v.payload_eligible P z width r banks src tab dst owners phase trial entry fitted timeMin s.large s.positive s.late
    pages.guard.header pages.checked.header maxWord first inspected
  have ceiling:=v.payload_guard_failure_ceiling P z width r banks src tab dst owners phase trial entry date positive s.late
    pages.guard.header pages.guard.scores s.limit
  have support:=v.payload_population P z width phase trial pre s.late
  have many:=v.selected_population P z width r banks src tab dst owners ev entry s.layout live π s.valid s.failed s.threshold support ceiling eligible
  have active:=v.payload_repair_live P z width r banks src tab dst owners phase trial entry fitted s
  have placed : (x).Placed := v.payload_spill_placed P z width r banks src tab dst owners phase trial entry fitted s
  have fee:=v.payload_charge_page P z width phase trial stage pages.charges
  apply v.payload_failed_packets P z width r banks src tab dst owners phase trial entry fitted s.layout live t timeMin s.positive s.large
    s.letterFit _ fee.1 fee.2 placed _ s.event s.failed many s.held s.rateRoom
  intro j keep
  obtain ⟨global,columns,horiz⟩:=geom.faces j (active j keep)
  exact v.payload_rowRead P z width r banks src tab dst owners phase trial entry fitted s.layout live j keep t positive s.threshold
    pages.guard.header pages.stage.header maxWord first last
    geom.headBefore geom.room wordPositive geom.order geom.loaded geom.codes geom.fits global columns horiz

end

section
set_option maxRecDepth 4096
variable (phase trial slice inner : ℕ) (entry : Memory (wordBits z (2^v.W) copies))
local notation "ev" => Attempt.inner phase trial slice inner
local notation "pre" => (guard C ev).apply entry
local notation "checked" => postSnapshot ((C).layout ev) (repair C ev) (prepared C ev entry)
local notation "stage" => v.stage P z width r banks src tab dst owners ev entry
local notation "t" => Calendar.time v.mesh v.finish ev
variable (fitted : v.purchasedStageSizes P z width r banks src tab dst owners phase trial slice inner entry)
local notation "x" => v.purchasedStageInput P z width r banks src tab dst owners phase trial slice inner entry fitted
local notation "π" => v.purchasedStage_compile P z width r banks src tab dst owners phase trial slice inner entry fitted
variable (s : v.RepairSlot P z width r banks src tab dst owners (.inner phase trial slice inner) entry)
local notation "live" => s.slot.currentReady
local notation "T" => v.selectedTape P z width r banks src tab dst owners ev entry s.layout live π
local notation "test" => v.purchasedTest P z width phase trial slice inner
local notation "sh" => ((bs).outer phase trial).market.shelf
local notation "S" => (bs).sampler
local notation "h₀" => stratumHeader z (2^v.W) k (S).degree v.depth ((bs).stratumHeader phase trial)

set_option maxHeartbeats 2000000 in
include fitted s in
def purchased_repair (geom : v.PurchasedRepairGeometry P z width r banks src tab dst owners phase trial slice inner entry)
    (maxWord : (H).bought.maxWord<2^W)
    (perm : Equiv.Perm (Fin (2^z))) (headLow : (h₀).stop≤(arena).base v.mesh (.attempt ev))
    (born : PurchasedBirth sh S perm v.depth ((bs).stratumHeader phase trial) entry k)
    : (A).bank.FailedRows (2^z) width v.actualK v.keepLimit v.loss v.menu.margin t
      ((A).read (Succession v.mesh (.attempt ev)).1 entry)
      ((A).read (Succession v.mesh (.attempt ev)).2 (after C (.attempt ev) entry)) := by
  classical
  have wordPositive : 0<W := by unfold wordBits; omega
  have date:=dateInTable_of_event v.mesh ev s.event
  have timeMin : (v.finish:ℝ)/2≤t := (v.real_times date.1).2 slice
  have positive : 0<t := (half_pos (show 0<(v.finish:ℝ) by exact_mod_cast v.clock.finish_pos)).trans_le timeMin
  have pages:=s.pages
  have room:=v.purchased_table_room z s.late
  have saved:=v.row_buffer_stock P z width r banks src tab dst owners ev entry live bills
  have first:=v.row_quote_cells P z width bills ev entry pre date pages.guard.header.scalar pages.guard.scores
    room.2.2.2 (fun i=>(saved i).1) s.limit
  have inspected:=v.row_quote_cells P z width bills ev entry checked date pages.checked.header.scalar pages.checked.scores
    room.2.2.2 (fun i=>(saved i).2.1) s.limit
  have last:=v.row_quote_cells P z width bills ev entry stage date pages.stage.header.scalar pages.stage.scores
    room.2.2.2 (fun i=>(saved i).2.2) s.limit
  let archive:=v.purchased_row_archive P z width r banks src tab dst owners phase trial slice inner entry perm live headLow born
  have witness := v.purchased_archive_live_rows P z width r banks src tab dst owners phase trial slice inner
    entry perm s.late archive
  have eligible:=v.purchased_eligible P z width r banks src tab dst owners phase trial slice inner entry fitted timeMin s.large s.positive s.late
    pages.guard.header pages.checked.header maxWord first inspected perm archive.preHeader archive.checkedHeader archive.preTiles archive.checkedTiles witness
  have ceiling:=v.purchased_guard_failure_ceiling P z width r banks src tab dst owners phase trial slice inner entry date positive s.late
    pages.guard.header pages.guard.scores s.limit perm archive.preHeader archive.preTiles witness
  have support:=v.purchased_population P z width r banks src tab dst owners phase trial slice inner s.late perm entry born
  have many:=v.selected_population P z width r banks src tab dst owners ev entry s.layout live π s.valid s.failed s.threshold support ceiling eligible
  have active:=v.purchased_repair_live P z width r banks src tab dst owners phase trial slice inner entry fitted s
  have placed : (x).Placed := v.purchased_spill_placed P z width r banks src tab dst owners phase trial slice inner entry fitted s perm headLow born
  have fee:=v.purchased_charge_page P z width phase trial slice inner stage pages.charges
  apply v.purchased_failed_packets P z width r banks src tab dst owners phase trial slice inner entry fitted s.layout live t timeMin s.positive s.large
    s.letterFit _ fee.1 fee.2 placed _ s.event s.failed many s.held s.rateRoom
  intro j keep
  obtain ⟨global,columns,horiz,birth⟩:=geom.faces j (active j keep)
  exact v.purchased_rowRead P z width r banks src tab dst owners phase trial slice inner entry fitted s.layout live j keep t positive s.threshold
    pages.guard.header pages.stage.header maxWord first last perm archive.preHeader archive.stageHeader archive.preTiles archive.stageTiles (witness j (active j keep)) s.late
    geom.headBefore geom.room wordPositive geom.order geom.loaded geom.codes geom.fits global columns horiz birth

end
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI

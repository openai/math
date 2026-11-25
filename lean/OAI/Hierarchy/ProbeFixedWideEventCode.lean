import OAI.Hierarchy.ProbeFixedWideSettlementPage
import OAI.Hierarchy.ProbeFixedTerminalStock
import OAI.Hierarchy.ProbeFixedPaidDirectoryShapes
import OAI.Hierarchy.ProtocolRAMCalendarPaidSlices

namespace OAI
/-! # Chronological paid-width transaction lists for the original signed chart -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires StockCommit
open scoped Classical Fin.CommRing

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "s" => v.nativeBoards P h width
local notation "A" => v.privateArena P h width
local notation "D" => 2^v.W
local notation "N" => Stages h D
local notation "r" => Fintype.card (Slots h D k)
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

def widePaidSlices (maxBroadcastBits : ℕ) : List PaidWidths.Slice :=
  let fmt:=v.nativeFormats P h width
  let layout:=FeedLayout.atEvent («N»:=N) v.mesh A fmt (P).joint.initial width v.keepLimit
  let feeds:=feedColumns («N»:=N) v.mesh A fmt (P).joint.initial width v.keepLimit
  let sink:=(P).catalogue.sink r banks src tab dst owners
  paidSlices v.mesh fmt feeds sink (P).catalogue.idBase (fun a=>(StripChart.header F s a).fieldTerm)
    (StripChart.id F s (P).catalogue) (v.nativeTrees P h width)
    (v.paidSpillPath P h width (routeBanks start cnt r) route order)
    (v.paidFeedPath P h width route layout) maxBroadcastBits

def wideEventSlices (maxBroadcastBits : ℕ) : Event→List PaidWidths.Slice :=
  let fmt:=v.nativeFormats P h width
  let layout:=FeedLayout.atEvent («N»:=N) v.mesh A fmt (P).joint.initial width v.keepLimit
  let feeds:=feedColumns («N»:=N) v.mesh A fmt (P).joint.initial width v.keepLimit
  let sink:=(P).catalogue.sink r banks src tab dst owners
  eventSlices fmt feeds sink (P).catalogue.idBase (fun a=>(StripChart.header F s a).fieldTerm)
    (StripChart.id F s (P).catalogue) (v.nativeTrees P h width)
    (v.paidSpillPath P h width (routeBanks start cnt r) route order)
    (v.paidFeedPath P h width route layout) maxBroadcastBits

theorem wideEventSlices_flat (bits : ℕ) :
    (events v.mesh).flatMap (v.wideEventSlices h width bits)=v.widePaidSlices h width bits := rfl


end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI

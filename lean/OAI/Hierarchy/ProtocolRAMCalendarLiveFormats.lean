import OAI.Hierarchy.ProtocolRAMNativeLiveFormats
import OAI.Hierarchy.ProtocolRAMCalendarOccurrenceSource
import OAI.Hierarchy.ProtocolRAMCalendarScoreFormat

namespace OAI
/-! # Resolving the preceding live stock before compiling all strip expressions -/

namespace Hierarchy.ProtocolRAM.Calendar
open AdaptiveProbe ProbeStage ProbeStage.Native
noncomputable section
variable {z d k q goods N : ℕ}

section
variable (c : Mesh) (arena : Arena) (initial : ℕ)
  (build : Attempt→ℕ→Format z d k q goods)

theorem live_area (capacity : ∀a addr,(build a addr).pricedArea=(build a initial).pricedArea) (a : Attempt) :
    (liveFormats c arena initial build a).pricedArea=(build a initial).pricedArea := by
  exact capacity a _

theorem live_published (capacity : ∀a addr,(build a addr).pricedArea=(build a initial).pricedArea) :
    publishedStock c arena (liveFormats c arena initial build)=
      publishedStock c arena (fun a=>build a initial) := by
  funext e
  cases e with
  | feed _ => rfl
  | attempt a =>
    exact congrArg StockCommit.Area.output (live_area c arena initial build capacity a)

theorem live_stock (capacity : ∀a addr,(build a addr).pricedArea=(build a initial).pricedArea)
    (address : ∀a addr,(build a addr).market.shelf.stockBase=addr)
    (a : Attempt) (i : Commodity (Fin (2^z)) N k) :
    stockAt c arena (liveFormats c arena initial build) initial a i=
      (liveFormats c arena initial build a).market.shelf.stockBase+PurchaseInventory.slot i := by
  rw [stockAt,live_published c arena initial build capacity]
  change resolvedStock c arena initial build a+_=(build a (resolvedStock c arena initial build a)).market.shelf.stockBase+_
  rw [address]

theorem live_feed (capacity : ∀a addr,(build a addr).pricedArea=(build a initial).pricedArea) (width cap : ℕ)
    (u : Boundary) :
    feedColumns (N:=N) c arena (liveFormats c arena initial build) initial width cap u=
      feedColumns (N:=N) c arena (fun a=>build a initial) initial width cap u := by
  cases u <;> simp only [feedColumns,FeedLayout.atEvent,live_area c arena initial build capacity,
    live_published c arena initial build capacity]

end
end
end Hierarchy.ProtocolRAM.Calendar

end OAI

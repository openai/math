import OAI.Hierarchy.ProbeFixedRepairFits
import OAI.Hierarchy.ProbeFixedStockOperands
import OAI.Hierarchy.ProbeFixedNativeStockRun

namespace OAI
/-! # A fitted native paid strip on every admitted dated ballot -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard StripChart StockCommit
open StripDirectory CatalystArchive PurchaseStage
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} [Nonempty (Fin k)] {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width r : ℕ)
  (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
set_option quotPrecheck false
local notation "W" => wordBits z (2^v.W) copies
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "B" => v.nativeBoards P z width
local notation "G" => v.privateArena P z width
local notation "H" => v.publicHeader P z width
local notation "g" => v.stamp P z width r banks src tab dst owners
local notation "f" => v.nativeFormats P z width
local notation "incoming" => resolvedStock v.mesh G P.joint.initial (build F B)


open CatalystArchive
omit [Nonempty (Fin k)] in
theorem paid_stage_header (a : Attempt) (init entry : Memory W) (prior tail : List Event)
    (slot : Slot C init (.attempt a) prior tail entry) («public» : (H).Resident init) :
    (StripChart.header F B a).Loaded (v.stage P z width r banks src tab dst owners a entry) := by
  let h:=StripChart.header F B a
  have old : h=(H).ports.header 0 := by
    cases a <;> simp only [PortROM.Table.header,Fin.val_zero,Nat.zero_mul,Nat.add_zero] <;> rfl
  have original : h.Loaded init:=old.symm ▸ «public».ports 0
  have low : h.stop≤(G).first := old.symm ▸ (((H).ports.end_le 0).trans (v.stock_port_room P z width))
  have inSlot : h.Loaded entry:=original.frame (by
    intro x _ hx
    rw [←slot.entry]
    apply run_frame C _ init x slot.prefixReady
    intro ev _
    exact (v.event_prefix P z width r banks src tab dst owners ev x ((hx.trans_le low).trans_le (Nat.le_add_right ..))).1)
  have floor : (G).first≤(G).base v.mesh (.attempt a) := Nat.le_add_right ..
  have room : h.stop≤(g a).out:=low.trans (floor.trans (v.stock_label P z width a))
  apply retained_header C a entry (f a).pricedArea (f a).stockSource (g a) slot.currentReady h inSlot room
    (show (g a).out≤(f a).pricedArea.start from Nat.le_add_right ..)
  intro x _ hx
  exact (v.event_prefix P z width r banks src tab dst owners (.attempt a) x ((hx.trans_le low).trans_le floor)).1


set_option maxHeartbeats 1000000 in
omit [Nonempty (Fin k)] in
theorem payload_paid_fit (phase trial : ℕ) (init entry : Memory W) (prior tail : List Event)
    (slot : Slot C init (.attempt (.outer phase trial)) prior tail entry) («public» : (H).Resident init)
    (late : v.stripHeight≤z) (small : width≤2^z) :
    v.payloadStageSizes P z width r banks src tab dst owners phase trial entry := by
  let ev:=Attempt.outer phase trial
  let batch:=enabledBatch (f ev).market.layout (f ev).board
  have commit : (C).commit ev=pricedSegment (f ev).pricedArea (f ev).stockSource (g ev) W batch:=rfl
  have room:=v.payload_size_room P z width C entry (g ev) (f ev).stockSource batch phase trial (incoming ev)
    late small slot.currentReady commit
  apply StripSizes.of_header room
  exact v.paid_stage_header P z width r banks src tab dst owners ev init entry prior tail slot «public»


omit [Nonempty (Fin k)] in
theorem purchased_paid_fit (phase trial slice inner : ℕ) (init entry : Memory W) (prior tail : List Event)
    (slot : Slot C init (.attempt (.inner phase trial slice inner)) prior tail entry) («public» : (H).Resident init)
    (late : v.stripHeight≤z) (small : width≤2^z) :
    v.purchasedStageSizes P z width r banks src tab dst owners phase trial slice inner entry := by
  let ev:=Attempt.inner phase trial slice inner
  let batch:=enabledBatch (f ev).market.layout (f ev).board
  have commit : (C).commit ev=pricedSegment (f ev).pricedArea (f ev).stockSource (g ev) W batch:=rfl
  have room:=v.purchased_size_room P z width C entry (g ev) (f ev).stockSource batch phase trial slice inner (incoming ev)
    late small slot.currentReady commit
  apply StripSizes.of_header room
  exact v.paid_stage_header P z width r banks src tab dst owners ev init entry prior tail slot «public»

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI

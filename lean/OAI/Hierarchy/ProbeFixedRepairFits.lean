import OAI.Hierarchy.ProbeFixedRepairSlot
import OAI.Hierarchy.ProbeFixedNativeStrips
import OAI.Hierarchy.ProbeFixedStripSizes

namespace OAI
/-! # Deriving the fitted row board of each paid attempt from the installed words -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard StripChart StockCommit
open StripDirectory CatalystArchive PurchaseStage
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} [Nonempty (Fin k)] {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width r : ℕ)
  (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "W" => wordBits z (2^v.W) copies
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "B" => v.nativeBoards P z width
local notation "G" => v.privateArena P z width
local notation "H" => v.publicHeader P z width
local notation "g" => v.stamp P z width r banks src tab dst owners
local notation "f" => v.nativeFormats P z width
local notation "incoming" => resolvedStock v.mesh G P.joint.initial (build F B)

section
variable (phase trial : ℕ) (entry : Memory (wordBits z (2^v.W) copies))
local notation "ev" => Attempt.outer phase trial
local notation "stage" => v.stage P z width r banks src tab dst owners ev entry

set_option maxHeartbeats 1000000 in
omit [Nonempty (Fin k)] in
theorem payload_fit_at_slot (s : v.RepairSlot P z width r banks src tab dst owners ev entry)
    (size : width≤2^z) : v.payloadStageSizes P z width r banks src tab dst owners phase trial entry := by
  let batch:=enabledBatch (f ev).market.layout (f ev).board
  have commit : (C).commit ev=pricedSegment (f ev).pricedArea (f ev).stockSource (g ev) W batch:=rfl
  have room:=v.payload_size_room P z width C entry (g ev) (f ev).stockSource batch
    phase trial (incoming ev) s.late size s.slot.currentReady commit
  apply StripSizes.of_header room
  change (StripChart.header F B ev).Loaded stage
  have eq : StripChart.header F B ev=(H).ports.header 0 := by
    simp only [PortROM.Table.header,Fin.val_zero,Nat.zero_mul,Nat.add_zero]; rfl
  rw [eq]
  exact s.pages.stage.header.ports 0
end

section
variable (phase trial slice inner : ℕ) (entry : Memory (wordBits z (2^v.W) copies))
local notation "ev" => Attempt.inner phase trial slice inner
local notation "stage" => v.stage P z width r banks src tab dst owners ev entry

omit [Nonempty (Fin k)] in
theorem purchased_fit_at_slot (s : v.RepairSlot P z width r banks src tab dst owners ev entry)
    (size : width≤2^z) : v.purchasedStageSizes P z width r banks src tab dst owners phase trial slice inner entry := by
  let batch:=enabledBatch (f ev).market.layout (f ev).board
  have commit : (C).commit ev=pricedSegment (f ev).pricedArea (f ev).stockSource (g ev) W batch:=rfl
  have room:=v.purchased_size_room P z width C entry (g ev) (f ev).stockSource batch
    phase trial slice inner (incoming ev) s.late size s.slot.currentReady commit
  apply StripSizes.of_header room
  change (StripChart.header F B ev).Loaded stage
  have eq : StripChart.header F B ev=(H).ports.header 0 := by
    simp only [PortROM.Table.header,Fin.val_zero,Nat.zero_mul,Nat.add_zero]; rfl
  rw [eq]
  exact s.pages.stage.header.ports 0
end
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI

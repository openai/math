import OAI.Hierarchy.DescentTerminalRowArenaSort
import OAI.Hierarchy.ProtocolRAMGeneratedWrite

namespace OAI
/-! # External words above the offset and stable sorting passes -/
namespace Hierarchy.DescentTerminalRowArena.Arena
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM

variable (A : Arena) {w : ℕ}

theorem offset_after (m : Memory w) {x : ℕ} (high : A.finish≤x) :
    DescentTerminalSiteOffsets.result A.offset A.sites m x=m x := by
  have stride := A.stride_min
  have endAt : A.offset.offsets.base+A.sites ≤ x :=
    ((Nat.add_le_add_left (show A.sites≤A.stride by omega) (A.atBand 13)).trans
      (A.band_after (show 13<22 by decide))).trans high
  exact ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inr endAt)

theorem sorted_after (m : Memory w) (positive : 0<A.sites) (low : A.Lower w)
    (fit : A.finish<2^w) {x : ℕ} (high : A.finish≤x) :
    DescentTerminalExteriorPackets.sorted A.homes A.order A.sites A.packets positive m x=m x := by
  have room := (A.sort_room low fit).fits
  have stride := A.stride_min
  have last : A.order.sorted+A.packets≤x :=
    ((Nat.add_le_add_left (show A.packets≤A.stride by omega) (A.atBand 17)).trans
      (A.band_after (show 17<22 by decide))).trans high
  have src := room.src_safe
  have counts := room.count_safe
  have starts := room.prefix_safe
  unfold DescentTerminalExteriorPackets.sorted
  refine (ProtocolRAMEndpointSort.frame _ room _ _ x (.inr (by omega)) (.inr (by omega)) (.inr last)).trans ?_
  exact ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inr (by omega : A.order.src+A.packets≤x))

theorem slot_after (m : Memory w) {x : ℕ} (high : A.finish≤x) :
    DescentTerminalPacketSlotRAM.after A.order A.packets A.sites m x=m x :=
  DescentTerminalPacketSlotRAM.retained _ _ _ _ _ (.inr (A.slot_end_le.trans high))

/-- The original data are still visible after all three physical writing phases. -/
theorem sockets_after (m : Memory w) (positive : 0<A.sites) (low : A.Lower w)
    (fit : A.finish<2^w) {x : ℕ} (high : A.finish≤x) :
    DescentTerminalPacketSlotRAM.after A.order A.packets A.sites
      (DescentTerminalExteriorPackets.sorted A.homes A.order A.sites A.packets positive
        (DescentTerminalSiteOffsets.result A.offset A.sites m)) x=m x :=
  (A.slot_after _ high).trans ((A.sorted_after _ positive low fit high).trans (A.offset_after m high))

end Hierarchy.DescentTerminalRowArena.Arena

end OAI

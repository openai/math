import OAI.Hierarchy.DescentTerminalRowArena
import OAI.Hierarchy.DescentTerminalPacketSlotFrame
import OAI.Hierarchy.DescentTerminalSiteOffsets

namespace OAI
/-! # Word addresses for site offsets and stable packet sorting in the terminal row arena -/
namespace Hierarchy.DescentTerminalRowArena.Arena
open ProtocolRAM

variable (A : Arena) {w : ℕ}

/-- Compute all site offsets in the bank following the row plan. -/
def offset : DescentTerminalSiteOffsets.Layout := ⟨A.row.siteFirst,A.modulo,A.bank 13⟩

/-- Four successive banks contain packet homes, site counts, exclusive starts and sorted packet indices. -/
def order : ProtocolRAMEndpointSort.Layout := ⟨A.atBand 14,A.atBand 15,A.atBand 16,A.atBand 17⟩

theorem offset_room (low : A.Lower w) (fit : A.finish<2^w) :
    DescentTerminalSiteOffsets.Room A.offset w A.sites := by
  refine ⟨A.fits_band fit (show 5<13 by decide) (by decide),A.lower_band low.modulo 13,?_⟩
  have stride := A.stride_min
  exact A.end_word fit (show 13<22 by decide) (by omega)

theorem sort_room (low : A.Lower w) (fit : A.finish<2^w) :
    DescentTerminalExteriorPackets.SortRoom A.homes A.order w A.packets A.sites := by
  have stride := A.stride_min
  change A.start+22*A.stride<2^w at fit
  refine ⟨A.lower_band low.homes 14,⟨?_,?_,?_,?_⟩,?_⟩
  · change A.start+14*A.stride+A.packets≤A.start+15*A.stride
    omega
  · change A.start+15*A.stride+A.sites≤A.start+16*A.stride
    omega
  · change A.start+16*A.stride+A.sites+1≤A.start+17*A.stride
    omega
  · change A.start+17*A.stride+A.packets<2^w
    omega
  · omega

/-- The actual padded source and site spans and the last full packet column fit inside the arena. -/
theorem slot_end_le : DescentTerminalPacketSlotRAM.out A.order A.packets A.sites + A.packets ≤ A.finish := by
  have space := DescentTerminalPacketSlotRAM.workspace A.order A.packets A.sites
  have stride := A.stride_min
  change _ ≤ A.start+17*A.stride+3*A.packets+2*A.sites+4 at space
  change _ ≤ A.start+22*A.stride
  omega

theorem slot_room (_low : A.Lower w) (fit : A.finish<2^w) :
    DescentTerminalPacketSlotRAM.out A.order A.packets A.sites + A.packets < 2^w :=
  A.slot_end_le.trans_lt fit

theorem finish_le : A.finish ≤ A.start+88*(A.sites+A.rows+A.packets+1) := by
  have size := ProtocolRAMPurchaseSampler.span_le (2*A.sites+A.rows+A.packets+1)
  change A.stride ≤ 2*((2*A.sites+A.rows+A.packets+1)+1) at size
  change A.start+22*A.stride ≤ _
  omega

end Hierarchy.DescentTerminalRowArena.Arena

end OAI

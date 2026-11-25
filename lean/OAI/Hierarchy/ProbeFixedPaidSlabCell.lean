import OAI.Hierarchy.ProbeFixedPostings
import OAI.Hierarchy.ProtocolRAMCalendarRemainders
import OAI.Hierarchy.ProtocolRAMCalendarVerdict

namespace OAI
/-! # Preservation of the original paid slab through later native events -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native StripChart
open scoped Fin.CommRing Classical
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width r : ℕ)
  (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "N" => CoreBoard.Stages z (2^v.W)
local notation "W" => wordBits z (2^v.W) copies
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "G" => v.privateArena P z width
local notation "f" => v.nativeFormats P z width

/-- Every word below the current slab's upper end survives to the same
original checkout. This covers the priced attempt output and the feed rows. -/
theorem paid_slab_cell (e : Event) (mem entry : Memory W) (prior tail : List Event)
    (cut : Slot C mem e prior tail entry) (x : ℕ)
    (inside : x<(G).base v.mesh e+(G).stride) :
    checkedOut C ((G).endAddress v.mesh) mem x=after C e entry x := by
  have live : e∈events v.mesh := by change _∈events (C).mesh; rw [cut.events]; simp
  have flag := inside.trans_le ((G).within v.mesh e live)
  rw [checkedOut,ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl flag)]
  apply cut.word
  intro t ht
  exact (v.event_prefix P z width r banks src tab dst owners t x
    (inside.trans_le ((G).apart v.mesh (cut.later t ht)))).1

/-- The actual checkout preserves every individual spill word of the committed
attempt, in all native modes. -/
theorem paid_attempt_cell_at (a : Attempt) (mem entry : Memory W) (prior tail : List Event)
    (cut : Slot C mem (.attempt a) prior tail entry) (i : Fin (f a).pricedArea.goods) :
    let area := (f a).pricedArea
    let addr := area.output+area.goods+area.goods+i.val
    checkedOut C ((G).endAddress v.mesh) mem addr=after C (.attempt a) entry addr := by
  intro area addr
  apply v.paid_slab_cell P z width r banks src tab dst owners _ mem entry prior tail cut
  have span := v.attempt_room P z width a
  change area.output+3*area.goods≤(G).base v.mesh (.attempt a)+(G).stride at span
  change area.output+area.goods+area.goods+i.val<_
  have localRow : i.val<area.goods:=i.isLt
  omega

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI

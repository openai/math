import OAI.Hierarchy.ProtocolRAMCalendarEconomicSize
import OAI.Hierarchy.ProtocolRAMCalendarEconomicBoot

namespace OAI
/-! # Addressing the complete header already bounds every integer lookup key -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native
open scoped Classical Fin.CommRing

theorem DiscrepancyROM.Table.entries_lt_stop {p D : ℕ} (t : DiscrepancyROM.Table p D) (pos : 0<p) :
    t.entries<t.stop := by
  have inside : t.entries<t.size:=ProtocolRAMPurchaseSampler.lt_span _
  have full:=Nat.mul_le_mul_right t.size pos
  change 1*t.size≤p*t.size at full
  rw [one_mul] at full
  exact inside.trans_le (full.trans (Nat.le_add_left ..))

namespace StripChart.EconomicHeader
variable {phases X Y steps w : ℕ}

theorem fits_of_stop (E : EconomicHeader phases X Y steps) (ord : E.Ordered)
    (pos : 0<phases) (room : E.stop≤2^w) : E.Fits w := by
  have all:=ord.menuOrdered
  obtain ⟨m₁,m₂,m₃⟩:=all
  have s₁ : E.scalar.kinds*E.scalar.stride<E.scalar.size:=ProtocolRAMPurchaseSampler.lt_span _
  have s₂:=Nat.mul_le_mul_right E.scalar.size pos
  change 1*E.scalar.size≤phases*E.scalar.size at s₂
  rw [one_mul] at s₂
  have stone : E.scalar.kinds*E.scalar.stride<E.scalar.stop:=s₁.trans_le (s₂.trans (Nat.le_add_left ..))
  have a:=E.payload.entries_lt_stop pos
  have b:=E.bought.entries_lt_stop pos
  have l:=E.menus.left.entries_lt_stop pos
  have r:=E.menus.right.entries_lt_stop pos
  have α:=E.menus.leftAlphabet.entries_lt_stop (by decide)
  have β:=E.menus.rightAlphabet.entries_lt_stop (by decide)
  have u₁ : E.payload.base≤E.payload.stop:=Nat.le_add_right ..
  have u₂ : E.bought.base≤E.bought.stop:=Nat.le_add_right ..
  have u₃ : E.menus.left.base≤E.menus.left.stop:=Nat.le_add_right ..
  have u₄ : E.menus.right.base≤E.menus.right.stop:=Nat.le_add_right ..
  have u₅ : E.menus.leftAlphabet.base≤E.menus.leftAlphabet.stop:=Nat.le_add_right ..
  have u₆ : E.menus.rightAlphabet.base≤E.menus.rightAlphabet.stop:=Nat.le_add_right ..
  have u₇ : E.payloadTree.base≤E.payloadTree.stop:=Nat.le_add_right ..
  have u₈ : E.boughtTree.base≤E.stop:=Nat.le_add_right ..
  obtain ⟨_,o₁,o₂,o₃,_,o₄,o₅⟩:=ord
  change E.bought.stop=E.menus.left.base at o₃
  change E.menus.rightAlphabet.stop=E.payloadTree.base at o₄
  constructor <;> omega

end StripChart.EconomicHeader
end Hierarchy.ProtocolRAM.Calendar
end

end OAI

import OAI.Hierarchy.ProtocolRAMCalendarEconomicBootFrame

namespace OAI
/-! # The economic public ROM preserves each higher terminal or private source word -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.StripChart.EconomicHeader
open Computability.VPVNP.BurstRAM PrivateRAM
variable {phases X Y steps w : ℕ}

theorem tail_words (E : EconomicHeader phases X Y steps) (ord : E.Ordered) (rest : Memory w) (x : ℕ)
    (hi : E.stop≤x) : E.scalar.words (E.vectorMemory rest) x=rest x := by
  have pt : E.payloadTree.stop≤x:=ord.boughtTreeBase.le.trans ((Nat.le_add_right ..).trans hi)
  have pb : E.payloadTree.base≤x:=(Nat.le_add_right ..).trans pt
  have ms : E.menus.stop≤x:=ord.payloadTreeBase.le.trans pb
  have bs : E.bought.stop≤x:=ord.menusBase.le.trans ((Ordered.menu_bounds E ord).trans ms)
  have os : E.payload.stop≤x:=ord.boughtBase.le.trans ((Nat.le_add_right ..).trans bs)
  have ss : E.scalar.stop≤x:=ord.payloadBase.le.trans ((Nat.le_add_right ..).trans os)
  rw [E.scalar.frame _ x (.inr ss),E.tree_origin ord rest x pb]
  exact (E.boughtTree.frame (E.payloadTree.words rest) x (.inr hi)).trans (E.payloadTree.frame rest x (.inr pt))

end Hierarchy.ProtocolRAM.Calendar.StripChart.EconomicHeader
end

end OAI

import OAI.Hierarchy.ProbeDiscrepancyLayout
import OAI.Hierarchy.ProtocolRAMCalendarStripMenuBoot
import OAI.Hierarchy.ProtocolRAMCalendarStripTrees
import OAI.Hierarchy.ProtocolRAMCalendarStripArena

namespace OAI
/-! # One layout for the immutable inputs of every chronological repair and replay -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native
open scoped Classical Fin.CommRing

namespace MenuROM
theorem Pages.above {phases X Y w : ℕ} (p : Pages phases X Y) (rest : Memory w) (ord : p.Ordered)
    (x : ℕ) (hi : p.stop≤ x) : p.words rest x=rest x := by
  have a : p.right.base≤ p.right.stop:=Nat.le_add_right ..
  have b : p.leftAlphabet.base≤ p.leftAlphabet.stop:=Nat.le_add_right ..
  have c : p.rightAlphabet.base≤ p.rightAlphabet.stop:=Nat.le_add_right ..
  have h₄ : p.rightAlphabet.stop≤ x:=hi
  have h₃ := ord.third.trans (c.trans h₄)
  have h₂ := ord.second.trans (b.trans h₃)
  have h₁ := ord.first.trans (a.trans h₂)
  dsimp only [Pages.words,DiscrepancyROM.both]
  rw [p.rightAlphabet.outside _ (.inr h₄),p.leftAlphabet.outside _ (.inr h₃),p.right.outside _ (.inr h₂),p.left.outside _ (.inr h₁)]
end MenuROM

namespace StripChart
open CoreBoard StockCommit CatalogueRows
variable {z W k q depth phases jobs X Y steps w : ℕ}

structure EconomicHeader (phases X Y steps : ℕ) where
  ports : PortROM.Table 1
  scalar : ScalarROM.Table phases
  payload : DiscrepancyROM.Table phases X
  bought : DiscrepancyROM.Table phases Y
  menus : MenuROM.Pages phases X Y
  payloadTree : PortROM.Table steps
  boughtTree : PortROM.Table steps

namespace EconomicHeader
variable (H : EconomicHeader phases X Y steps)

def stop := H.boughtTree.stop
def slab (extra : ℕ) : Slab := ⟨H.stop,extra⟩

def treeMemory (rest : Memory w) := H.boughtTree.words (H.payloadTree.words rest)
def vectorMemory (rest : Memory w) := DiscrepancyROM.both H.payload H.bought (H.menus.words (H.treeMemory rest))
def words (b : JointHeader.Board) (z d N k : ℕ) (phase : Fin phases→PhasePrice) (π : Equiv.Perm (Fin (2^z)))
    (stock : ℕ→ℕ) (rest : Boot.Tape z d) := JointHeader.words b z d N k phase π stock
      (H.ports.words (H.scalar.words (H.vectorMemory rest)))

structure Ordered : Prop where
  scalarBase : H.ports.stop=H.scalar.base
  payloadBase : H.scalar.stop=H.payload.base
  boughtBase : H.payload.stop=H.bought.base
  menusBase : H.bought.stop=H.menus.base
  menuOrdered : H.menus.Ordered
  payloadTreeBase : H.menus.stop=H.payloadTree.base
  boughtTreeBase : H.payloadTree.stop=H.boughtTree.base

theorem tree_origin (order : H.Ordered) (rest : Memory w) (x : ℕ) (low : H.payloadTree.base≤ x) :
    H.vectorMemory rest x=H.treeMemory rest x := by
  have mlo : H.menus.base≤ H.menus.stop := by
    rcases order.menuOrdered with ⟨a,b,c⟩
    change H.menus.left.base≤ H.menus.rightAlphabet.stop
    exact (Nat.le_add_right ..).trans (a.trans ((Nat.le_add_right ..).trans (b.trans ((Nat.le_add_right ..).trans (c.trans (Nat.le_add_right ..))))))
  have bought : H.bought.stop≤ x:=order.menusBase.le.trans (mlo.trans (order.payloadTreeBase.le.trans low))
  have payload : H.payload.stop≤ x:=order.boughtBase.le.trans ((Nat.le_add_right ..).trans bought)
  dsimp only [vectorMemory,DiscrepancyROM.both]
  rw [H.bought.outside _ (.inr bought),H.payload.outside _ (.inr payload),H.menus.above _ order.menuOrdered _ (order.payloadTreeBase.le.trans low)]

theorem tree_before (order : H.Ordered) (rest : Memory w) (x : ℕ) (hi : x< H.payloadTree.base) :
    H.treeMemory rest x=rest x := by
  dsimp only [treeMemory]
  have high:=hi.trans_le ((Nat.le_add_right .. : H.payloadTree.base≤ H.payloadTree.stop).trans order.boughtTreeBase.le)
  rw [H.boughtTree.frame _ _ (.inl high),H.payloadTree.frame _ _ (.inl hi)]

end EconomicHeader

local notation "d" => 2^W
local notation "N" => Stages z (2^W)

variable (F : Type*) [Field F] [SiteNaming (ColumnSite (PayloadStrip.Columns (Stages z (2^W))) k)]
  [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)]
  (s : Boards z (2^W) k q depth) (t : TreeCosts) (c : Mesh) (joint : JointHeader.Board)
  (catalogue : Board) (G : PortBanks ((c.inject+c.cool)*c.outerFuel))
  (finish : ℝ) (price : PhasePrice) (R S Q T : ℕ)

def economicHeader : EconomicHeader (DeadlineROM.count c) (Fintype.card (PayloadStrip.Quotes N k))
    (Fintype.card (ChainStrip.Axes depth k)) (events c).length :=
  let phase:=DeadlineROM.prices c finish price
  let p:=portTable s (JointHeader.stop joint z N k (DeadlineROM.count c))
  let scalar:=priceTable s joint c finish price
  let old:=outerVector F s joint c finish price R Q
  let next:=innerVector F s joint c finish price R S Q T
  let menus:=menuPages F s t next.stop R S phase
  ⟨p,scalar,old,next,menus,payloadPage s c catalogue G F menus.stop,boughtPage s c catalogue G F menus.stop⟩

theorem economic_ordered : (economicHeader F s t c joint catalogue G finish price R S Q T).Ordered :=
  ⟨rfl,rfl,rfl,rfl,menu_ordered F s t _ _ _ _,rfl,rfl⟩

end StripChart
end Hierarchy.ProtocolRAM.Calendar
end

end OAI

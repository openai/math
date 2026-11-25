import OAI.Hierarchy.ProtocolRAMCalendarEconomicHeader

namespace OAI
/-! # All economic price, choice, packet and tree pages read from one bounded native boot -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.StripChart.EconomicHeader
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native
open scoped Fin.CommRing Classical
variable {phases X Y steps z d N k jobs w : ℕ}
variable (H : EconomicHeader phases X Y steps)

structure Fits (w : ℕ) : Prop where
  scalar : H.scalar.kinds*H.scalar.stride<2^w
  payload : H.payload.entries≤2^w
  bought : H.bought.entries≤2^w
  menu₁ : H.menus.left.entries≤2^w
  menu₂ : H.menus.right.entries≤2^w
  packet₁ : H.menus.leftAlphabet.entries≤2^w
  packet₂ : H.menus.rightAlphabet.entries≤2^w

structure Resident (m : Memory w) : Prop where
  ports : ∀i,(H.ports.header i).Loaded m
  scalar : H.scalar.Resident m
  payload : H.payload.Resident m
  bought : H.bought.Resident m
  menus : H.menus.Resident m
  payloadTree : ∀i,(H.payloadTree.header i).Loaded m
  boughtTree : ∀i,(H.boughtTree.header i).Loaded m

theorem origin (ord : H.Ordered) (b : JointHeader.Board) (phase : Fin phases→PhasePrice)
    (π : Equiv.Perm (Fin (2^z))) (stock : ℕ→ℕ) (rest : Boot.Tape z d) (markets : Fin jobs→Market z d k)
    {size : ℕ} (layout : Boot.Layout markets size) (hd : 1≤ d) (first : 2^z≤ b.initial)
    (score : JointHeader.stop b z N k phases≤ H.ports.base) (heap : heapEnd z d copies≤ H.ports.base)
    (fits : H.Fits (wordBits z d copies)) (room : H.stop<2^wordBits z d copies)
    (before : ∀i,H.stop≤ Boot.low (markets i)) (length : H.stop≤ size) :
    H.Resident (Boot.booted markets size (H.words b z d N k phase π stock rest)) := by
  let trees:=H.treeMemory rest
  let choices:=H.menus.words trees
  let data:=H.vectorMemory rest
  let out:=Boot.booted markets size (H.words b z d N k phase π stock rest)
  have end0 : H.boughtTree.base≤ H.stop:=Nat.le_add_right ..
  have end1 : H.payloadTree.stop≤ H.stop:=ord.boughtTreeBase.le.trans end0
  have end2 : H.menus.stop≤ H.stop:=ord.payloadTreeBase.le.trans ((Nat.le_add_right ..).trans end1)
  have mlo : H.menus.base≤ H.menus.stop := by
    rcases ord.menuOrdered with ⟨a,b,c⟩
    exact (Nat.le_add_right ..).trans (a.trans ((Nat.le_add_right ..).trans (b.trans ((Nat.le_add_right ..).trans (c.trans (Nat.le_add_right ..))))))
  have end3 : H.bought.stop≤ H.stop:=ord.menusBase.le.trans (mlo.trans end2)
  have end4 : H.scalar.stop≤ H.stop:=ord.payloadBase.le.trans ((Nat.le_add_right ..).trans
    (ord.boughtBase.le.trans ((Nat.le_add_right ..).trans end3)))
  have end5 : H.ports.stop≤ H.stop:=ord.scalarBase.le.trans ((Nat.le_add_right ..).trans end4)
  have hdig : 0< wordBits z d copies := by unfold wordBits;omega
  have oldNew:=DiscrepancyROM.master b phase π stock choices H.ports H.scalar H.payload H.bought markets layout
    hd first score heap ord.scalarBase.le ord.payloadBase.le ord.boughtBase.le (fun i=>end3.trans (before i))
    (end3.trans length) fits.payload fits.bought
  have menu:=H.menus.master ord.menuOrdered b phase π stock trees H.ports H.scalar H.payload H.bought markets layout
    hd first score heap ord.scalarBase.le ord.payloadBase.le ord.boughtBase.le ord.menusBase.le
    (fun i=>end2.trans (before i)) (end2.trans length) fits.menu₁ fits.menu₂ fits.packet₁ fits.packet₂
  have stable (x : ℕ) (lo : H.payloadTree.base≤ x) (hi : x< H.stop) : out x=trees x := by
    have scalarLow:=ord.payloadBase.le.trans ((Nat.le_add_right ..).trans (ord.boughtBase.le.trans
      ((Nat.le_add_right ..).trans (ord.menusBase.le.trans (mlo.trans (ord.payloadTreeBase.le.trans lo))))))
    exact (JointHeader.tail_origin b phase π stock data H.ports H.scalar markets layout hd first score heap
      ord.scalarBase.le x scalarLow (fun i=>hi.trans_le (before i)) (hi.trans_le length)).trans (H.tree_origin ord rest x lo)
  refine ⟨JointHeader.port_origin b phase π stock (H.scalar.words data) H.ports markets layout hd first score heap
    (end5.trans_lt room) (end5.trans length) (fun i=>end5.trans (before i)),
    JointHeader.scalar_origin b phase π stock data H.ports H.scalar markets layout hd first score heap
      ord.scalarBase.le (end4.trans length) (fun i=>end4.trans (before i)) fits.scalar,
    oldNew.1,oldNew.2,menu,?_,?_⟩
  · intro i
    apply (H.payloadTree.loaded rest hdig (end1.trans_lt room) i).frame
    intro x lo hi
    have lower : H.payloadTree.base≤ x:=(Nat.le_add_right ..).trans lo
    have upper : x< H.payloadTree.stop:=hi.trans_le (H.payloadTree.end_le i)
    exact (stable x lower (upper.trans_le end1)).trans (H.boughtTree.frame _ x (.inl (upper.trans_le ord.boughtTreeBase.le)))
  · intro i
    apply (H.boughtTree.loaded (H.payloadTree.words rest) hdig room i).frame
    intro x lo hi
    apply stable
    · have low : H.boughtTree.base≤ x:=(Nat.le_add_right ..).trans lo
      exact (Nat.le_add_right ..).trans (ord.boughtTreeBase.le.trans low)
    · exact hi.trans_le (H.boughtTree.end_le i)

end Hierarchy.ProtocolRAM.Calendar.StripChart.EconomicHeader
end

end OAI

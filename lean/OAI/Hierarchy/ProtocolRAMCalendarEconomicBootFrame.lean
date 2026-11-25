import OAI.Hierarchy.ProtocolRAMCalendarEconomicBoot

namespace OAI
/-! # The actual lower subdivision and catalogue input coexists with every upper economic page -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.StripChart.EconomicHeader
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native
open scoped Classical Fin.CommRing
variable {phases X Y steps z d N k jobs w : ℕ}
variable (H : EconomicHeader phases X Y steps)

theorem Ordered.menu_bounds (ord : H.Ordered) : H.menus.base≤H.menus.stop := by
  rcases ord.menuOrdered with ⟨a,b,c⟩
  exact (Nat.le_add_right ..).trans (a.trans ((Nat.le_add_right ..).trans (b.trans ((Nat.le_add_right ..).trans (c.trans (Nat.le_add_right ..))))))

theorem upper_frame (ord : H.Ordered) {m out : Memory w} (installed : H.Resident m)
    (ports : ∀i,(H.ports.header i).Loaded out)
    (same : ∀x,H.scalar.base≤x→x<H.stop→ out x=m x) : H.Resident out := by
  have one : H.scalar.base≤H.scalar.stop:=Nat.le_add_right ..
  have two : H.payload.base≤H.payload.stop:=Nat.le_add_right ..
  have three : H.bought.base≤H.bought.stop:=Nat.le_add_right ..
  have four:=Ordered.menu_bounds H ord
  have five : H.payloadTree.base≤H.payloadTree.stop:=Nat.le_add_right ..
  have six : H.boughtTree.base≤H.boughtTree.stop:=Nat.le_add_right ..
  rcases ord with ⟨o₁,o₂,o₃,o₄,om,o₅,o₆⟩
  unfold stop at same
  refine ⟨ports,installed.scalar.frame ?_,installed.payload.frame ?_,installed.bought.frame ?_,
    installed.menus.move om ?_,?_,?_⟩
  · intro x lo hi;exact same x lo (by omega)
  · intro x lo hi;exact same x (by omega) (by omega)
  · intro x lo hi;exact same x (by omega) (by omega)
  · intro x lo hi;exact same x (by omega) (by omega)
  · intro i
    apply (installed.payloadTree i).frame
    intro x lo hi
    have lower : H.payloadTree.base≤x:=(Nat.le_add_right ..).trans lo
    have upper:=hi.trans_le (H.payloadTree.end_le i)
    exact same x (by omega) (by omega)
  · intro i
    apply (installed.boughtTree i).frame
    intro x lo hi
    have lower : H.boughtTree.base≤x:=(Nat.le_add_right ..).trans lo
    exact same x (by omega) (hi.trans_le (H.boughtTree.end_le i))

theorem origin_with_low (ord : H.Ordered) (b : JointHeader.Board) (phase : Fin phases→PhasePrice)
    (π : Equiv.Perm (Fin (2^z))) (stock : ℕ→ℕ) (rest : Boot.Tape z d) (markets : Fin jobs→Market z d k)
    {size : ℕ} (layout : Boot.Layout markets size) (hd : 1≤d) (first : 2^z≤b.initial)
    (score : JointHeader.stop b z N k phases≤H.ports.base) (heap : heapEnd z d copies≤H.ports.base)
    (fits : H.Fits (wordBits z d copies)) (room : H.stop<2^wordBits z d copies)
    (before : ∀i,H.stop≤Boot.low (markets i)) (length : H.stop≤ size)
    (low : Boot.Tape z d→Boot.Tape z d) (above : ∀m x,H.scalar.base≤x→low m x=m x) :
    let high:=H.scalar.words (H.vectorMemory rest)
    let mixed:=JointHeader.words b z d N k phase π stock (H.ports.words (low high))
    H.Resident (Boot.booted markets size mixed) := by
  intro high mixed
  have original:=H.origin ord b phase π stock rest markets layout hd first score heap fits room before length
  have top : H.ports.stop≤H.stop:=by
    have a : H.scalar.base≤H.scalar.stop:=Nat.le_add_right ..
    have u : H.payload.base≤H.payload.stop:=Nat.le_add_right ..
    have v : H.bought.base≤H.bought.stop:=Nat.le_add_right ..
    have s:=Ordered.menu_bounds H ord
    have t : H.payloadTree.base≤H.payloadTree.stop:=Nat.le_add_right ..
    have f : H.boughtTree.base≤H.stop:=Nat.le_add_right ..
    rcases ord with ⟨o₁,o₂,o₃,o₄,_,o₅,o₆⟩
    omega
  apply H.upper_frame ord original (JointHeader.port_origin b phase π stock (low high) H.ports markets layout hd first
    score heap (top.trans_lt room) (top.trans length) (fun i=>top.trans (before i)))
  intro x lo hi
  have early : H.ports.stop≤x:=ord.scalarBase.le.trans lo
  have active : H.ports.base≤x:=(Nat.le_add_right ..).trans early
  have output (mem : Boot.Tape z d) :
      Boot.booted markets size (JointHeader.words b z d N k phase π stock (H.ports.words mem)) x=mem x := by
    let words:=JointHeader.words b z d N k phase π stock (H.ports.words mem)
    have entered:=(Boot.start markets layout hd π words (JointHeader.authentic (N:=N) (k:=k) b phase π stock _ first)).2
    have keep:=entered.kept x (heap.trans active) (fun i reach=>Nat.not_lt_of_ge reach.1 (hi.trans_le (before i)))
    rw [Computability.VPVNP.RAMMemory.initialMemory,ite_eq_left (hi.trans_le length)] at keep
    exact keep.trans ((JointHeader.tail_words b phase π stock (H.ports.words mem) x first (score.trans active)).trans
      (H.ports.frame mem x (.inr early)))
  exact (output (low high)).trans ((above high x lo).trans (output high).symm)

end Hierarchy.ProtocolRAM.Calendar.StripChart.EconomicHeader
end

end OAI

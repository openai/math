import OAI.Hierarchy.DiscrepancyPaddedCap
import OAI.Hierarchy.ProtocolRAMCalendarChargePages

namespace OAI
/-! # All physical recommendation slots retain their menu bounds across the initial boot -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native
open LinearAlgebra.SpectralBooks.ChordGraph
open ThreeFlat.RAM
open scoped Classical Fin.CommRing

theorem MenuROM.Pages.recommendation_caps {phases U V w leftCap rightCap : ℕ}
    (p : MenuROM.Pages phases U V) (rest : Memory w) (order : p.Ordered)
    (l : ∀i a,p.left.word i a≤leftCap) (r : ∀i a,p.right.word i a ≤ rightCap) :
    p.left.Capped leftCap (p.words rest) ∧ p.right.Capped rightCap (p.words rest) := by
  have a := p.left.capped_words rest l
  have b := p.right.capped_words (p.left.words rest) r
  have before : p.leftAlphabet.base≤p.rightAlphabet.base :=
    (Nat.le_add_right .. : p.leftAlphabet.base≤p.leftAlphabet.stop).trans order.third
  have lower (x : ℕ) (hx : x<p.leftAlphabet.base) :
      p.words rest x=p.right.words (p.left.words rest) x :=
    (p.rightAlphabet.outside _ (.inl (hx.trans_le before))).trans (p.leftAlphabet.outside _ (.inl hx))
  have leftEnd : p.left.stop≤p.leftAlphabet.base :=
    order.first.trans ((Nat.le_add_right .. : p.right.base≤p.right.stop).trans order.second)
  exact ⟨a.transport (fun x _ hx=>(lower x (hx.trans_le leftEnd)).trans
    (p.right.outside _ (.inl (hx.trans_le order.first)))),
    b.transport (fun x _ hx=>lower x (hx.trans_le order.second))⟩

namespace StripChart.EconomicHeader
variable {phases X Y steps z d k jobs N : ℕ} (H : EconomicHeader phases X Y steps)

theorem recommendation_origin {leftCap rightCap : ℕ} (ord : H.Ordered) (b : JointHeader.Board) (phase : Fin phases→PhasePrice)
    (π : Equiv.Perm (Fin (2^z))) (stock : ℕ→ℕ) (rest : Boot.Tape z d)
    (markets : Fin jobs→Market z d k) {size : ℕ} (layout : Boot.Layout markets size)
    (hd : 1≤d) (first : 2^z≤b.initial) (score : JointHeader.stop b z N k phases≤H.ports.base)
    (heap : heapEnd z d copies≤H.ports.base) (length : H.stop ≤ size)
    (before : ∀i,H.stop≤Boot.low (markets i))
    (low : Boot.Tape z d→Boot.Tape z d) (above : ∀m x,H.scalar.base≤x→low m x=m x)
    (l : ∀i a,H.menus.left.word i a≤leftCap) (r : ∀i a,H.menus.right.word i a ≤ rightCap) :
    let high:=H.scalar.words (H.vectorMemory rest)
    let mixed:=JointHeader.words b z d N k phase π stock (H.ports.words (low high))
    let output:=Boot.booted markets size mixed
    H.menus.left.Capped leftCap output ∧ H.menus.right.Capped rightCap output := by
  intro high mixed output
  have caps:=H.menus.recommendation_caps (H.treeMemory rest) ord.menuOrdered l r
  have prec : H.bought.stop≤H.menus.left.base:=ord.menusBase.le
  have endCap : H.menus.rightAlphabet.stop≤H.stop := ord.payloadTreeBase.le.trans
    ((Nat.le_add_right ..).trans (ord.boughtTreeBase.le.trans (Nat.le_add_right ..)))
  have fromMenu (x : ℕ) (start : H.menus.left.base≤x) (last : x<H.menus.rightAlphabet.stop) :
      output x=H.menus.words (H.treeMemory rest) x := by
    have bought:=prec.trans start
    have payload:=ord.boughtBase.le.trans ((Nat.le_add_right ..).trans bought)
    have scalar:=ord.payloadBase.le.trans ((Nat.le_add_right ..).trans payload)
    have scalarStart : H.scalar.base≤x:=(Nat.le_add_right ..).trans scalar
    have ports:=ord.scalarBase.le.trans scalarStart
    have bottom : H.ports.base≤x:=(Nat.le_add_right ..).trans ports
    have hi:= last.trans_le endCap
    have entered:=(Boot.start markets layout hd π mixed
      (JointHeader.authentic (N:=N) (k:=k) b phase π stock _ first)).2
    have keep:=entered.kept x (heap.trans bottom) (fun i here=>Nat.not_lt_of_ge here.1 (hi.trans_le (before i)))
    rw [Computability.VPVNP.RAMMemory.initialMemory,ite_eq_left (hi.trans_le length)] at keep
    calc
      output x = mixed x := keep
      _ = H.ports.words (low high) x :=
        JointHeader.tail_words b phase π stock (H.ports.words (low high)) x first (score.trans bottom)
      _ = low high x := H.ports.frame (low high) x (.inr ports)
      _ = high x := above high x scalarStart
      _ = H.vectorMemory rest x := H.scalar.frame (H.vectorMemory rest) x (.inr scalar)
      _ = H.menus.words (H.treeMemory rest) x := by
        dsimp only [vectorMemory,DiscrepancyROM.both]
        rw [H.bought.outside _ (.inr bought),H.payload.outside _ (.inr payload)]
  have rightEnd : H.menus.right.stop≤H.menus.rightAlphabet.stop :=
    ord.menuOrdered.second.trans ((Nat.le_add_right ..).trans (ord.menuOrdered.third.trans (Nat.le_add_right ..)))
  have leftEnd : H.menus.left.stop≤H.menus.right.stop := ord.menuOrdered.first.trans (Nat.le_add_right ..)
  have leftStart : H.menus.left.base≤H.menus.right.base :=
    (Nat.le_add_right ..).trans ord.menuOrdered.first
  exact ⟨caps.1.transport (fun x hx hi=>fromMenu x hx (hi.trans_le (leftEnd.trans rightEnd))),
    caps.2.transport (fun x hx hi=>fromMenu x (leftStart.trans hx) (hi.trans_le rightEnd))⟩
end StripChart.EconomicHeader

end Hierarchy.ProtocolRAM.Calendar
end

end OAI

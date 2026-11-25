import OAI.Hierarchy.DiscrepancyPaddedCap
import OAI.Hierarchy.ProtocolRAMCalendarChargePages
import OAI.Hierarchy.TaggedWireCausalTape

namespace OAI
/-! # Alphabet bounds on every physical packet word, including every padded address -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native
open LinearAlgebra.SpectralBooks.ChordGraph
open ThreeFlat.RAM
open scoped Classical Fin.CommRing
variable {p D w q : ℕ}


namespace MenuROM
open StripDirectory DiscrepancyROM
variable {F E A : Type*} [Field F] [Fintype E] [Nonempty E] [Fintype A]
  {s : ℕ} [Nonempty (Fin s)] {edge : E→Chord s} {req : A→E}
  {box : Set (E→ℝ)} {ε tree : ℝ} {N : ℕ}

theorem alphabet_cap (m : Probe.FixedMenu F edge req box ε tree N) (base : ℕ)
    (size : ∀j,(m.packet j).terms≤q) :
    ∀i a,(alphabets m base).word i a≤q := by
  intro i a
  change alphabetWord m (a 0).val≤q
  cases h : (a 0).val with
  | zero => exact Nat.zero_le _
  | succ u =>
    simp only [alphabetWord]
    split
    · exact size _
    · exact Nat.zero_le _

theorem Pages.caps {phases U V : ℕ} (p : Pages phases U V) (rest : Memory w) (o : p.Ordered)
    (l : ∀i a,p.leftAlphabet.word i a≤q) (r : ∀i a,p.rightAlphabet.word i a≤q) :
    p.leftAlphabet.Capped q (p.words rest) ∧ p.rightAlphabet.Capped q (p.words rest) := by
  have left:=p.leftAlphabet.capped_words (both p.left p.right rest) l
  exact ⟨left.transport (fun x _ hi=>p.rightAlphabet.outside _ (.inl (hi.trans_le o.third))),
    p.rightAlphabet.capped_words _ r⟩
end MenuROM

namespace StripChart.EconomicHeader
variable {phases X Y steps z d k jobs N : ℕ} (H : EconomicHeader phases X Y steps)

theorem alphabet_origin (ord : H.Ordered) (b : JointHeader.Board) (phase : Fin phases→PhasePrice)
    (π : Equiv.Perm (Fin (2^z))) (stock : ℕ→ℕ) (rest : Boot.Tape z d)
    (markets : Fin jobs→Market z d k) {size : ℕ} (layout : Boot.Layout markets size)
    (hd : 1≤d) (first : 2^z≤b.initial) (score : JointHeader.stop b z N k phases≤H.ports.base)
    (heap : heapEnd z d copies≤H.ports.base) (length : H.stop≤ size)
    (before : ∀i,H.stop≤Boot.low (markets i))
    (low : Boot.Tape z d→Boot.Tape z d) (above : ∀m x,H.scalar.base≤x→low m x=m x)
    (l : ∀i a,H.menus.leftAlphabet.word i a≤q) (r : ∀i a,H.menus.rightAlphabet.word i a≤q) :
    let high:=H.scalar.words (H.vectorMemory rest)
    let mixed:=JointHeader.words b z d N k phase π stock (H.ports.words (low high))
    let output:=Boot.booted markets size mixed
    H.menus.leftAlphabet.Capped q output ∧ H.menus.rightAlphabet.Capped q output := by
  intro high mixed output
  have caps:=H.menus.caps (H.treeMemory rest) ord.menuOrdered l r
  have prec : H.bought.stop≤H.menus.leftAlphabet.base := by
    have x:=ord.menusBase
    have a : H.menus.left.base≤H.menus.left.stop:=Nat.le_add_right ..
    have b : H.menus.right.base≤H.menus.right.stop:=Nat.le_add_right ..
    exact x.le.trans (a.trans (ord.menuOrdered.first.trans (b.trans ord.menuOrdered.second)))
  have endCap : H.menus.rightAlphabet.stop≤H.stop := ord.payloadTreeBase.le.trans
    ((Nat.le_add_right ..).trans (ord.boughtTreeBase.le.trans (Nat.le_add_right ..)))
  have fromMenu (x : ℕ) (start : H.menus.leftAlphabet.base≤x) (last : x<H.menus.rightAlphabet.stop) :
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
    have menu : H.vectorMemory rest x=H.menus.words (H.treeMemory rest) x := by
      dsimp only [vectorMemory,DiscrepancyROM.both]
      rw [H.bought.outside _ (.inr bought),H.payload.outside _ (.inr payload)]
    exact keep.trans ((JointHeader.tail_words b phase π stock (H.ports.words (low high)) x first
      (score.trans bottom)).trans ((H.ports.frame (low high) x (.inr ports)).trans
      ((above high x scalarStart).trans ((H.scalar.frame (H.vectorMemory rest) x (.inr scalar)).trans menu))))
  have order:=ord.menuOrdered.third
  exact ⟨caps.1.transport (fun x hx hi=>fromMenu x hx (hi.trans_le (order.trans (Nat.le_add_right ..)))),
    caps.2.transport (fun x hx hi=>fromMenu x ((Nat.le_add_right ..).trans (order.trans hx)) hi)⟩
end StripChart.EconomicHeader
/-- At an arbitrary reached attempt, even a malformed or missing menu code
selects a bounded alphabet word from the padded, physically initialized bank. -/
theorem measured_alphabet {goods digits : ℕ} (C : Chart w q goods) (es : List Event)
    (boot : Memory w) (a : Attempt) (t : DiscrepancyROM.Table 1 digits)
    (field : (C.raw a).batch.termCount=t.bank 0) (origin : t.Capped q boot)
    (past : mounted C es boot) (here : ready C (.attempt a) (run C es boot))
    (safe : ∀x,t.base≤x→x<t.stop→∀e∈(.attempt a::es),protected C x e)
    (i : Fin (C.layout a).candidates) :
    WireTelescope.CalendarTape.CounterROM.measured (C:=C) a (run C es boot) i≤q := by
  have h : t.Capped q (WireTelescope.HistogramShelf.snapshot C a (run C es boot)) := by
    apply origin.transport
    intro x lo hi
    exact (WireTelescope.HistogramShelf.snapshot_frame C a _ x here (safe x lo hi _ (List.mem_cons_self ..))).trans
      (run_frame C es boot x past (fun e he=>safe x lo hi e (List.mem_cons_of_mem _ he)))
  unfold WireTelescope.CalendarTape.CounterROM.measured
  rw [field]
  exact h.lookup _

end Hierarchy.ProtocolRAM.Calendar
end

end OAI

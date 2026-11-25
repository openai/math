import OAI.Computability.BorderVNP.TransmissionStartupArena
import OAI.Computability.BorderVNP.TransmissionPinsReplay

/-! # Physical reader words protected across the signed evaluator -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

open VPVNP.BurstRAM TeamContraction.ProcessorSlots

/-- The team selector and the four ordinary operands of the chosen matrix reader. -/
def readerControls : List ℕ := [0,19,28,29,30]

/-- The exact memory reads needed from before subtotal completion, excluding its newly
serialized tally. -/
def ReaderReads (A : StartupArena) (entryWords indexBits w a : ℕ) : Prop :=
  (∃ k ∈ readerControls, a=A.frame+k) ∨ (∃ i < entryWords*w, a=A.dense+i) ∨
  (∃ i < indexBits, a=A.ibase+i) ∨ (∃ i < indexBits, a=A.hbase+i)

/-- On the actual length allocation all four reader ranges end at or before the
first word reserved for subsequent directory and geometry computations. -/
theorem ReaderReads.below {A : StartupArena} {entries pins w x : ℕ}
    (h : ReaderReads A entries pins w x) (packet : entries*w ≤ A.copied) (pin : pins ≤ A.count) :
    x < A.next := by
  rcases h with ⟨k,hk,rfl⟩ | ⟨i,hi,rfl⟩ | ⟨i,hi,rfl⟩ | ⟨i,hi,rfl⟩
  all_goals simp only [StartupArena.next,StartupArena.hbase,StartupArena.ibase,StartupArena.broadcastBase,
    StartupArena.dense]
  · simp [readerControls] at hk; omega
  all_goals omega

/-- Every other primary field may be changed while these reader words are retained. -/
theorem ReaderReads.ne_field {A : StartupArena} {entries pins w x k : ℕ}
    (h : ReaderReads A entries pins w x) (small : k < 112) (other : k ∉ readerControls) : x ≠ A.frame+k := by
  rcases h with ⟨j,hj,rfl⟩ | ⟨i,_,rfl⟩ | ⟨i,_,rfl⟩ | ⟨i,_,rfl⟩
  · intro eq; exact other ((Nat.add_left_cancel eq) ▸ hj)
  all_goals simp only [StartupArena.hbase,StartupArena.ibase,StartupArena.broadcastBase,StartupArena.dense]; omega

/-- The team selector, reader operands and packed gate advice survive from boot.
The two indexed inputs survive from the actual substituted and live pin snapshot. -/
structure ReaderKept {w : ℕ} (A : StartupArena) (entryWords indexBits : ℕ)
    (boot postPin final : Memory w) : Prop where
  control : ∀ k ∈ readerControls, final (A.frame+k)=boot (A.frame+k)
  dense : ∀ i < entryWords*w, final (A.dense+i)=boot (A.dense+i)
  row : ∀ i < indexBits, final (A.ibase+i)=postPin (A.ibase+i)
  col : ∀ i < indexBits, final (A.hbase+i)=postPin (A.hbase+i)

/-- The team selector tested by the final reader is the team installed by
the boot frame, for every team and every returning run. -/
theorem ReaderKept.teamAt {w entries pins : ℕ} {A : StartupArena} {l : Pins.Layout}
    {pub : Arg → Word w} {boot postPin final : Memory w}
    (kept : ReaderKept A entries pins boot postPin final)
    (head : (pub 0).val=A.frame) (frame : Pins.Frame l (readings pub) (readings boot)) :
    (final (pub 0).val).val=l.team := by
  have retained : final (pub 0).val=boot (pub 0).val := by
    simpa only [head,Nat.add_zero] using kept.control 0 (by decide)
  exact (congrArg Fin.val retained).trans frame.team

/-- A verified RAM update preserving the addressed reads advances the snapshot. -/
theorem ReaderKept.advance {w : ℕ} {A : StartupArena} {entries pins : ℕ} {boot pinMem before after : Memory w}
    (h : ReaderKept A entries pins boot pinMem before)
    (same : ∀ a, ReaderReads A entries pins w a → after a=before a) :
    ReaderKept A entries pins boot pinMem after := by
  refine ⟨fun k hk => (same _ (Or.inl ⟨k,hk,rfl⟩)).trans (h.control k hk),
    fun i hi => (same _ (Or.inr (Or.inl ⟨i,hi,rfl⟩))).trans (h.dense i hi),
    fun i hi => (same _ (Or.inr (Or.inr (Or.inl ⟨i,hi,rfl⟩)))).trans (h.row i hi),
    fun i hi => (same _ (Or.inr (Or.inr (Or.inr ⟨i,hi,rfl⟩)))).trans (h.col i hi)⟩

/-- The native pin loop stores only in the two high, disjoint input arrays. At its
actual exit both the original gate advice and the four ordinary boot words persist. -/
theorem ReaderKept.of_prepared {w : ℕ} (A : StartupArena) (p : Pins.Layout) (bits : ℕ → Bool)
    (boot : Memory w) (entries pins : ℕ) (packet : entries*w ≤ A.copied)
    (ibase : p.ibase=A.ibase) (hbase : p.hbase=A.hbase) :
    let m := Pins.preparedMemory p bits boot p.count
    ReaderKept A entries pins boot m m := by
  intro m
  have low (x : ℕ) (hx : x<A.ibase) : m x=boot x := by
    apply Pins.preparedMemory_other
    · intro i _; rw [ibase]; omega
    · intro i _ _; rw [hbase]; unfold StartupArena.hbase; omega
  refine ⟨?_,?_,fun _ _ => rfl,fun _ _ => rfl⟩
  · intro k hk; apply low; simp [readerControls] at hk
    unfold StartupArena.ibase StartupArena.broadcastBase StartupArena.dense; omega
  · intro i hi; apply low; unfold StartupArena.ibase StartupArena.broadcastBase; omega

end RoutingISA

end BorderVNP
end Computability
end OAI

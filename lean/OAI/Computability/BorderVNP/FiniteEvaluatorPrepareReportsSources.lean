import OAI.Computability.BorderVNP.FiniteEvaluatorPrepareReportsReady
import OAI.Computability.BorderVNP.CellTeamPreparedPaths

/-! # Physical sources of finite cell packets after report guessing and task placement

The supplied boundary bits arrive before the report pass. The report code appends
its guesses at the canonical offset. The typed task builder publishes the argument
row and preserves the combined bank, original geometry and zero supplement counts.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.Reports

open VPVNP.BurstRAM RoutingISA RoutingISA.CellPacket RoutingISA.CellPacket.Supplement
open CellSparse CellSparse.Packet TeamRAM

variable {Site : Type} {w : ℕ}

/-- Physical readback of the whole argument's supplied bank, including the
boundary delivered before the guess pass and the subsequently appended bits. -/
theorem source_after_tasks (l : Layout) (b : TypedTaskBuilder.Layout) (early late : List Row)
    (r : Row) (supplied : List Bool) (initial after : Memory w)
    (published : readings after=b.published (image l (early++r::late) (readings initial)))
    (width : r.canonical=supplied.length) (incoming : CompactWrite.Source initial r.base supplied)
    (sep : r.Separated l) (apart : ∀ z ∈ late, ∀ a, ¬ r.Outside l a → z.Outside l a)
    (incomingApart : ∀ i < supplied.length, ∀ z ∈ early++r::late, z.Outside l (r.base+i))
    (taskApart : ∀ i < (supplied++r.bits).length, ¬ b.outputAt (r.base+i)) :
    CompactWrite.Source after r.base (supplied++r.bits) := by
  intro i hi
  change readings after (r.base+i)=_
  rw [published,Batch.task_published_outside _ _ _ (taskApart i hi)]
  by_cases left : i < supplied.length
  · rw [List.getElem_append_left left,image_outside _ _ _ (incomingApart i left)]
    exact incoming i left
  · have len : i-supplied.length < r.bits.length := by rw [List.length_append] at hi; omega
    have right : supplied.length ≤ i := by omega
    rw [List.getElem_append_right right]
    have get := (final_readback l early late r (readings initial) sep apart).2.2.2 ⟨i-supplied.length,len⟩
    simpa only [Row.start,width,Fin.getElem_fin,show r.base+supplied.length+(i-supplied.length)=r.base+i by omega] using get

/-- The true bit width and the two zero private sidecar counters survive
publication of the compact seven-word task directory. -/
theorem counters_after_tasks (l : Layout) (b : TypedTaskBuilder.Layout) (early late : List Row)
    (r : Row) (initial after : Memory w)
    (published : readings after=b.published (image l (early++r::late) (readings initial)))
    (sep : r.Separated l) (apart : ∀ z ∈ late, ∀ a, ¬ r.Outside l a → z.Outside l a)
    (taskApart : ∀ a ∈ [l.tails+r.number,l.counters+2*r.number,l.counters+2*r.number+1], ¬ b.outputAt a) :
    readings after (l.tails+r.number)=r.bits.length ∧ readings after (l.counters+2*r.number)=0 ∧
      readings after (l.counters+2*r.number+1)=0 := by
  have eq (a : ℕ) (h : a ∈ [l.tails+r.number,l.counters+2*r.number,l.counters+2*r.number+1]) :
      readings after a=image l (early++r::late) (readings initial) a := by
    rw [published,Batch.task_published_outside _ _ _ (taskApart _ h)]
  have h := final_readback l early late r (readings initial) sep apart
  exact ⟨(eq _ (by simp)).trans h.1,(eq _ (by simp)).trans h.2.1,(eq _ (by simp)).trans h.2.2.1⟩

/-- Static source words of this owned cell, excluding its subsequently guessed
bits, the runtime counter words, and the task builder's output row. -/
def staticAt (o : Batch.Owned Site) (controls i a : ℕ) : Prop :=
  (controls+4*i ≤ a ∧ a < controls+4*i+4) ∨ a=o.layout.tail+1 ∨ a=o.layout.tail+2 ∨
  (o.placed.descriptorBase ≤ a ∧ a < o.placed.descriptorBase+(CellPacket.descriptors (prefixChunks o.placed)).length) ∨
  (∃ c ∈ prefixChunks o.placed, c.base ≤ a ∧ a < c.endSource) ∨
  (o.geometry ≤ a ∧ a < o.geometry+(fieldList record o.placed.rows++fieldList vector o.placed.reports).length)

/-- Geometry controls, public record list and previously delivered private boxes
present before the report pass and the seven-word task producer. -/
structure Static (o : Batch.Owned Site) (controls i : ℕ) (m : ℕ → ℕ) : Prop where
  /-- Four words selecting supplemental source, counter, merged count and report field count. -/
  controlsAt : WordsAt m (controls+4*i) [o.layout.supplement,o.layout.counters,o.layout.merged,o.layout.reportWords]
  /-- Geometry word addressed by the initial tail descriptor. -/
  tailBase : m (o.layout.tail+1)=o.geometry
  /-- Word count of the public rows and field-report metadata. -/
  tailLength : m (o.layout.tail+2)=1+(o.placed.rows.flatMap record).length+o.layout.reportWords
  /-- Public descriptors for the original private and public source chunks. -/
  descriptors : WordsAt m o.placed.descriptorBase (CellPacket.descriptors (prefixChunks o.placed))
  /-- Actual length-delimited box and natural-word contents referenced by the descriptors. -/
  boxes : ∀ c ∈ prefixChunks o.placed, c.Stored m
  /-- Public immutable sparse record and bit-major report-address lists. -/
  geometry : WordsAt m o.geometry (fieldList record o.placed.rows++fieldList vector o.placed.reports)

/-- The preparer establishes the complete pre-splice source certificate for
one genuinely owned finite cell. The old geometry supplies only immutable
fields. The seven-word task row, zero counts and scalar bits are obtained
from the two native stages' physical memory images. -/
theorem initial_after_tasks (l : Layout) (b : TypedTaskBuilder.Layout) (early late : List Row)
    (r : Row) (o : Batch.Owned Site) (controls i : ℕ) (supplied : List Bool) (initial after : Memory w)
    (published : readings after=b.published (image l (early++r::late) (readings initial)))
    (room : b.Room (image l (early++r::late) (readings initial)) w)
    (rank : i < b.before (image l (early++r::late) (readings initial)) b.cells)
    (task : let mem := image l (early++r::late) (readings initial)
      b.row mem (TypedTaskBuilder.globalCell b mem i)=TypedTaskBuilder.parameters o.typed)
    (old : Static o controls i (readings initial)) (clear : ∀ a, staticAt o controls i a →
      (∀ z ∈ early++r::late, z.Outside l a) ∧ ¬ b.outputAt a)
    (empty : o.extra=[]) (counter : o.layout.counters=l.counters+2*r.number)
    (report : o.layout.reportWords=(fieldList vector o.placed.reports).length)
    (prefixEnd : o.placed.descriptorBase+(CellPacket.descriptors (prefixChunks o.placed)).length=o.layout.tail)
    (mergeRoom : Batch.Room o.cell w) (typedRoom : o.typed.callRow+2 < 2^w ∧ o.typed.cell.Room w)
    (separateCount : o.layout.merged < o.layout.tail ∨ o.layout.tail+12 ≤ o.layout.merged)
    (start : o.placed.externalBase=r.base) (external : o.placed.external=supplied++r.bits)
    (width : r.canonical=supplied.length) (incoming : CompactWrite.Source initial r.base supplied)
    (sep : r.Separated l) (apart : ∀ z ∈ late, ∀ a, ¬ r.Outside l a → z.Outside l a)
    (incomingApart : ∀ j < supplied.length, ∀ z ∈ early++r::late, z.Outside l (r.base+j))
    (bank : ∀ j < (supplied++r.bits).length, ¬ b.outputAt (r.base+j))
    (countersApart : ∀ a ∈ [l.tails+r.number,l.counters+2*r.number,l.counters+2*r.number+1], ¬ b.outputAt a) :
    Batch.Initial o b.tasks controls i after := by
  have keep (a : ℕ) (ha : staticAt o controls i a) : readings after a=readings initial a := by
    rw [published,Batch.task_published_outside _ _ _ (clear a ha).2,image_outside _ _ _ (clear a ha).1]
  have counts := counters_after_tasks l b early late r initial after published sep apart countersApart
  refine ⟨TypedTaskBuilder.stored_parameters b _ room after published rank o.typed task,?_,
    (keep _ (.inr (.inl rfl))).trans old.tailBase,(keep _ (.inr (.inr (.inl rfl)))).trans old.tailLength,
    by simpa [empty,counter] using counts.2.1,by simpa [empty,counter] using counts.2.2,
    report,prefixEnd,?_,mergeRoom,typedRoom,separateCount⟩
  · intro j
    rw [keep _ (.inl ⟨Nat.le_add_right ..,Nat.add_lt_add_left j.isLt _⟩)]
    exact old.controlsAt j
  · refine ⟨?_,?_,?_,?_,?_⟩
    · intro j
      rw [keep _ (.inr (.inr (.inr (.inl ⟨Nat.le_add_right ..,Nat.add_lt_add_left j.isLt _⟩))))]
      exact old.descriptors j
    · intro c hc
      exact (old.boxes c hc).congr (fun a lo hi => keep a (.inr (.inr (.inr (.inr (.inl ⟨c,hc,lo,hi⟩))))))
    · intro j
      rw [keep _ (.inr (.inr (.inr (.inr (.inr ⟨Nat.le_add_right ..,Nat.add_lt_add_left j.isLt _⟩)))))]
      exact old.geometry j
    · rw [empty]; intro j; exact Fin.elim0 j
    · rw [start,external]
      exact source_after_tasks l b early late r supplied initial after published width incoming sep apart incomingApart bank

end FiniteEvaluator.Reports

end BorderVNP
end Computability
end OAI

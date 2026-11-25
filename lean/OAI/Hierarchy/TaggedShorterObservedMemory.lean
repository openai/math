import OAI.Hierarchy.TaggedShorterHistoryOrder
import OAI.Computability.VPVNP.RAMChain

namespace OAI
/-! # Binding the physical control ports to the final descriptor RAM image -/

noncomputable section
namespace Hierarchy.TaggedShorterObservedMemory
open ThreeFlat Diagonal
open Computability.VPVNP.BurstRAM Computability.VPVNP.RAMMemory Computability.VPVNP.RAMSerialization
open scoped Classical

variable {w : ℕ}

theorem correct_append (m : Memory w) (xs ys : List (Event w)) :
    Correct m (xs++ys) ↔ Correct m xs ∧ Correct (after m xs) ys :=
  Computability.VPVNP.BurstRAM.correct_append m xs ys

/-- One extra time slot reads each public output address. Repeated uses of a
word merely produce more read records. -/
def queries {N : ℕ} (addr value : Fin N → Word w) : List (Event w) :=
  List.ofFn fun i => Event.read (addr i) (value i)

theorem reads (m : Memory w) (l : List (Word w × Word w)) :
    Correct m (l.map (fun z => Event.read z.1 z.2)) ↔ ∀ pair ∈ l, pair.2=m pair.1.val := by
  induction l with
  | nil => simp [Correct]
  | cons pair l ih => simp [Correct,ih]

theorem data_words {N : ℕ} (m : Memory w) (xs : List (Event w)) (addr value : Fin N → Word w) :
    Correct m (xs++queries addr value) ↔
      Correct m xs ∧ ∀ i, value i=after m xs (addr i).val := by
  rw [correct_append]
  apply and_congr_right
  intro _
  simpa only [queries,List.map_ofFn,Function.comp_def,List.forall_mem_ofFn_iff] using
    reads (after m xs) (List.ofFn fun i => (addr i,value i))

theorem scan_reads {N m : ℕ} (hw : 2≤w) (S : ℕ) (header : ℕ → Word w)
    (es : List (Event w)) (addr value : Fin N → Word w) (fits : S+es.length+N≤2^m)
    (slots : Fin (2^m) → Option (WordRecord w))
    (chron : ∀ i, TraceSlots.toOrdered (slots i)=TraceRecordSort.inputWire S m header (es++queries addr value) i) :
    PaddedCheck none (List.ofFn fun i => (slots (TaggedShorterHistoryOrder.permutation hw slots i)).map WordRecord.record) ↔
      Correct (initialMemory S header) es ∧ ∀ i, value i=after (initialMemory S header) es (addr i).val := by
  refine (TaggedShorterHistoryOrder.scan_iff_correct hw S header _ ?_ slots chron).trans (data_words ..)
  simpa [queries,Nat.add_assoc] using fits

end Hierarchy.TaggedShorterObservedMemory

end
end OAI

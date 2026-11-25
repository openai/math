import OAI.ThreeFlat.Diagonal.TraceRecordSort
import OAI.Computability.VPVNP.RAMMessageBounds
import OAI.Computability.VPVNP.RAMSerialization

namespace OAI
/-! # The two-track distributed sort of a single RAM trace

Two logical input slots share each physical row. Sorting messages cross only
the fixed XOR edges in a Batcher layer. The one last-record field on a
consecutive-row edge enforces the read check at the block boundary.
-/

namespace ThreeFlat.Diagonal.TraceRecordSort

open Computability.VPVNP RAMMemory RAMSort BurstRAM RAMSerialization

variable {w : ℕ}

/-- Natural index view of the physical input wire array, extended by an empty slot. -/
def wire (S d : ℕ) (header : ℕ → Word w) (es : List (Event w)) (i : ℕ) : OrderedSlot (Word w) :=
  ⟨((raw S d header es)[i]?).join⟩

theorem flat_sortedBlock (S h d : ℕ) (header : ℕ → Word w) (es : List (Event w)) :
    RAMBoundary.flat (sortedBlock h d (wire S (h+d) header es)) = sorted S (h+d) header es := by
  let x := wire S (h+d) header es
  have hx : block (h+d) 0 x = inputWire S (h+d) header es := by
    funext i
    simp [block, x, wire, inputWire]
  have hs : block (h+d) 0 (runPhases (h+d) x) = sort (h+d) true (inputWire S (h+d) header es) := by
    simp only [block_runPhases, hx, Nat.zero_mod, decide_true]
  unfold sorted
  rw [← hs, List.map_ofFn]
  exact flatten_ofFn_blocks h d (fun i => (runPhases (h+d) x i).record)

/-- A row-local checker has one valid physical sorting assignment precisely
when the claimed reads agree with the native memory. -/
theorem twoTrack_at_iff (S d : ℕ) (header : ℕ → Word w) (es : List (Event w))
    (fits : S + es.length ≤ 2 ^ (1+d)) (m : MemoryMessages 1 d w) :
    (∀ v, MemoryAt m v (block 1 v.val (wire S (1+d) header es))) ↔
      m = actualMemoryMessages 1 d (wire S (1+d) header es) ∧ Correct (initialMemory S header) es := by
  rw [memoryAt_iff, flat_sortedBlock, sorted_iff_correct _ _ _ _ fits]

private theorem eventSlots_fitsWord (t : ℕ) (es : List (Event w)) (h : t + es.length ≤ 2^w)
    (r : Record (Word w)) (hr : some r ∈ eventSlots t es) : RecordFitsWord r := by
  induction es generalizing t with
  | nil => simp [eventSlots] at hr
  | cons e es ih =>
    simp only [eventSlots, List.mem_cons] at hr
    have hb : t+1 + es.length ≤ 2^w := by simp only [List.length_cons] at h; omega
    rcases hr with he | ht
    · cases e with
      | tick | choice => simp [eventSlot] at he
      | read a v | write a v =>
        simp only [eventSlot, Option.some.injEq] at he
        subst r
        exact ⟨a.isLt, show t < _ by omega, Nat.two_pow_pos _⟩
    · exact ih (t+1) hb ht

theorem wire_fitsWord (S d : ℕ) (header : ℕ → Word w) (es : List (Event w))
    (hs : S ≤ 2^w) (ht : es.length ≤ 2^w) (i : ℕ) (r : Record (Word w))
    (hr : r ∈ (wire S d header es i).record) : RecordFitsWord r := by
  change ((raw S d header es)[i]?).join = some r at hr
  by_cases hi : i < (raw S d header es).length
  · rw [List.getElem?_eq_getElem hi] at hr
    change (raw S d header es)[i] = some r at hr
    have hm : some r ∈ raw S d header es := hr ▸ List.getElem_mem hi
    simp [raw, List.mem_append] at hm
    rcases hm with hin | he
    · exact initialRecords_fitsWord header hs hin
    · exact eventSlots_fitsWord 0 es (by simpa) _ he
  · simp [List.getElem?_eq_none (Nat.le_of_not_gt hi)] at hr

theorem actual_twoTrack_fitsWord (S d : ℕ) (header : ℕ → Word w) (es : List (Event w))
    (hs : S ≤ 2^w) (ht : es.length ≤ 2^w) :
    (actualMemoryMessages 1 d (wire S (1+d) header es)).FitsWord := by
  let x := wire S (1+d) header es
  let P := fun a : OrderedSlot (Word w) => ∀ r ∈ a.record, RecordFitsWord r
  have hx : ∀ i, P (x i) := wire_fitsWord _ _ _ _ hs ht
  exact ⟨fun l v i => actual_sortSends_preserves _ _ hx l v i, fun j => runPhases_preserves _ hx _⟩

/-- Finite word slots sent along sorting edges and physical predecessor edges. -/
abbrev Packed (d w : ℕ) :=
  (RAMLayout.Layer d → Fin (2^d) → Fin 2 → Option (WordRecord w)) ×
    (Fin (2^d-1) → Option (WordRecord w))

def unpack {d : ℕ} (m : Packed d w) : MemoryMessages 1 d w :=
  ⟨fun l v j => ⟨(m.1 l v j).map WordRecord.record⟩, fun j => (m.2 j).map WordRecord.record⟩

private def pack {d : ℕ} (m : MemoryMessages 1 d w) (hm : m.FitsWord) : Packed d w :=
  (fun l v j => narrowSlot (m.sortSends l v j).record (hm.1 l v j),
   fun j => narrowSlot (m.lastRecords j) (hm.2 j))

private theorem unpack_pack {d : ℕ} (m : MemoryMessages 1 d w) (hm : m.FitsWord) :
    unpack (pack m hm) = m := by
  apply MemoryMessages.ext
  · funext l v j
    exact congrArg OrderedSlot.mk (widen_narrowSlot _ _)
  · funext j
    exact widen_narrowSlot _ _

private theorem unpack_injective {d : ℕ} : Function.Injective (unpack (w := w) (d := d)) := by
  have one : Function.Injective (Option.map (WordRecord.record (w := w))) := by
    intro x y h
    cases x <;> cases y <;> simp_all [WordRecord.record_injective.eq_iff]
  intro m n h
  apply Prod.ext
  · funext l v i
    exact one (congrArg (fun t : MemoryMessages 1 d w => (t.sortSends l v i).record) h)
  · funext j
    exact one (congrArg (fun t : MemoryMessages 1 d w => t.lastRecords j) h)

/-- Finite-word physical send assignments have exactly the same acceptance
multiplicity as chronological memory consistency. -/
theorem existsUnique_packed_iff (S d : ℕ) (header : ℕ → Word w) (es : List (Event w))
    (fits : S + es.length ≤ 2 ^ (1+d)) (hs : S ≤ 2^w) (ht : es.length ≤ 2^w) :
    (∃! m : Packed d w, ∀ v, MemoryAt (unpack m) v (block 1 v.val (wire S (1+d) header es))) ↔
      Correct (initialMemory S header) es := by
  constructor
  · rintro ⟨m,ha,_⟩
    exact ((twoTrack_at_iff _ _ _ _ fits _).mp ha).2
  · intro hc
    let m := actualMemoryMessages 1 d (wire S (1+d) header es)
    have hm : m.FitsWord := actual_twoTrack_fitsWord _ _ _ _ hs ht
    refine ⟨pack m hm, (twoTrack_at_iff _ _ _ _ fits _).mpr ⟨unpack_pack m hm, hc⟩, ?_⟩
    intro a ha
    apply unpack_injective
    rw [unpack_pack]
    exact ((twoTrack_at_iff _ _ _ _ fits _).mp ha).1

end ThreeFlat.Diagonal.TraceRecordSort

end OAI

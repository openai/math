import OAI.ThreeFlat.Diagonal.TraceSlotFormat
import OAI.ThreeFlat.Diagonal.TraceSortReplay

namespace OAI
/-! # Weighted binary witnesses on paired physical rows

CPU guesses occupy one fixed-width word bundle per step. Each sort layer's
outgoing record bundles and each last-record message have similarly fixed
positions. Successful RAM paths and successful binary witnesses have equal
weights, with every auxiliary sorting record uniquely determined.
-/

namespace ThreeFlat.Diagonal.TraceRows

open Computability.VPVNP BurstRAM RAMMemory RAMSort RAMSerialization

variable {w d : ℕ}

/-- Two physical outgoing record slots per row and layer. Each position
has seven key and payload words. An interior predecessor edge carries one slot. -/
abbrev SortBits (d w : ℕ) :=
  (Fin (RAMLayout.layerCount d) → Fin (2^d) → Fin 2 → Fin (7*w) → Bool) ×
    (Fin (2^d-1) → Fin (7*w) → Bool)

def writeSort (hw : 2 ≤ w) (m : TraceRecordSort.Packed d w) : SortBits d w :=
  (fun l v i => (TraceSlots.slotFormat hw).encode (m.1 ((RAMLayout.layerEquiv d).symm l) v i),
   fun j => (TraceSlots.slotFormat hw).encode (m.2 j))

def readSort (hw : 2 ≤ w) (bits : SortBits d w) : TraceRecordSort.Packed d w :=
  let parse := fun b => (TraceSlots.slotFormat hw).parse ((arrayBits 7 w).symm b)
  (fun l v i => parse (bits.1 ((RAMLayout.layerEquiv d) l) v i), fun j => parse (bits.2 j))

@[simp] theorem read_write_sort (hw : 2 ≤ w) (m : TraceRecordSort.Packed d w) :
    readSort hw (writeSort hw m) = m := by
  apply Prod.ext <;> funext _ <;> simp [readSort, writeSort, Format.encode]

def memoryPass (hw : 2 ≤ w) (S d : ℕ) (header : ℕ → Word w) (es : List (Event w))
    (z : SortBits d w) : Prop :=
  let m := readSort hw z
  writeSort hw m = z ∧ ∀ v, MemoryAt (TraceRecordSort.unpack m) v
    (block 1 v.val (TraceRecordSort.wire S (1+d) header es))

theorem existsUnique_memoryBits_iff (hw : 2 ≤ w) (S d : ℕ) (header : ℕ → Word w) (es : List (Event w))
    (fit : S+es.length ≤ 2^(1+d)) (hs : S ≤ 2^w) (ht : es.length ≤ 2^w) :
    (∃! bits : SortBits d w, memoryPass hw S d header es bits) ↔ Correct (initialMemory S header) es := by
  constructor
  · rintro ⟨z,hz,_⟩
    exact ((TraceRecordSort.twoTrack_at_iff _ _ _ _ fit _).mp hz.2).2
  · intro hc
    obtain ⟨m, hm, hu⟩ := (TraceRecordSort.existsUnique_packed_iff _ _ _ _ fit hs ht).mpr hc
    refine ⟨writeSort hw m, ?_, ?_⟩
    · simpa [memoryPass] using hm
    · intro z h
      rw [← h.1, hu (readSort hw z) h.2]

end ThreeFlat.Diagonal.TraceRows

end OAI

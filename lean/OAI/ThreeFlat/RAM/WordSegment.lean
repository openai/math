import OAI.ThreeFlat.RAM.Weighted
import Mathlib.Tactic

namespace OAI
/-! # Replacing a half-open segment of the external word array -/

namespace ThreeFlat.RAM

open Computability.VPVNP.BurstRAM

/-- The descriptor uses absolute addresses, which remain the same throughout
successive scans. All words outside the designated segment retain their values. -/
def fillSegment {w : ℕ} (start count : ℕ) (word : ℕ → Word w) (m : Memory w) : Memory w :=
  fun a => if start ≤ a ∧ a < start+count then word a else m a

@[simp] theorem fillSegment_zero {w : ℕ} (start : ℕ) (word : ℕ → Word w) (m : Memory w) :
    fillSegment start 0 word m = m := by
  funext a
  simp [fillSegment]

theorem fillSegment_succ {w : ℕ} (a : Word w) (n : ℕ) (word : ℕ → Word w) (m : Memory w) :
    fillSegment a.val (n+1) word m =
      fillSegment (a.val+1) n word (writeMemory m a (word a.val)) := by
  funext i
  by_cases h : i = a.val
  · subst i
    simp [fillSegment, writeMemory]
  · have range : (a.val ≤ i ∧ i < a.val+(n+1)) ↔
        (a.val+1 ≤ i ∧ i < (a.val+1)+n) := by omega
    simp [fillSegment, range, writeMemory, h]

theorem fillSegment_eq {w : ℕ} (start count : ℕ) (word : ℕ → Word w) (m target : Memory w)
    (inside : ∀ i, start ≤ i → i < start+count → word i = target i)
    (outside : ∀ i, i < start ∨ start+count ≤ i → m i = target i) :
    fillSegment start count word m = target := by
  funext i
  by_cases hi : start ≤ i ∧ i < start+count
  · simpa [fillSegment, hi] using inside i hi.1 hi.2
  · simpa [fillSegment, hi] using outside i (by omega)

end ThreeFlat.RAM

end OAI

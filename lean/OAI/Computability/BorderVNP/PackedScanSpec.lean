import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Log

/-! # Offsets in a table of wire bundles grouped by key

The inclusive total resets exactly at a change of key. In a sorted table it
sums the widths of the preceding and current records with that key.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedScan

/-- Inclusive width of the current contiguous run of equal keys. -/
def segmentTotal (key width : ℕ → ℕ) : ℕ → ℕ
  | 0 => width 0
  | j+1 => width (j+1) + if key (j+1) = key j then segmentTotal key width j else 0

/-- The width of the current row is included in the run total. -/
theorem width_le_total (key width : ℕ → ℕ) (j : ℕ) : width j ≤ segmentTotal key width j := by
  cases j with
  | zero => rfl
  | succ j => exact Nat.le_add_right _ _

/-- A prefix of at most `j+1` records of width at most `M` occupies at most `(j+1)*M` wires. -/
theorem total_le (key width : ℕ → ℕ) (M j : ℕ) (h : ∀ i ≤ j, width i ≤ M) :
    segmentTotal key width j ≤ (j+1)*M := by
  induction j with
  | zero => simpa [segmentTotal] using h 0 le_rfl
  | succ j ih =>
    have hp := ih (fun i hi => h i (Nat.le_succ_of_le hi))
    have hn := h (j+1) le_rfl
    rw [segmentTotal, Nat.succ_mul (j+1)]
    split <;> omega

/-- A sufficient binary working width for all run totals in the table. -/
def sumBits (rows M : ℕ) : ℕ := Nat.log2 (rows*M) + 1

/-- All segment totals fit the stated working width, including the all-zero case. -/
theorem total_fits (key width : ℕ → ℕ) (rows M : ℕ) (h : ∀ i < rows, width i ≤ M)
    (j : Fin rows) : segmentTotal key width j.val < 2 ^ sumBits rows M := by
  have ht := total_le key width M j (fun i hi => h i (lt_of_le_of_lt hi j.isLt))
  have hs : j.val+1 ≤ rows := j.isLt
  exact lt_of_le_of_lt (ht.trans (Nat.mul_le_mul_right M hs)) Nat.lt_log2_self

/-- On sorted keys the run total is the sum over all earlier rows with the current key,
including the current row. Sorting is required only on the prefix being inspected. -/
theorem total_eq_sum (key width : ℕ → ℕ) (j : ℕ)
    (sorted : ∀ i l, i ≤ l → l ≤ j → key i ≤ key l) :
    segmentTotal key width j = ∑ i ∈ Finset.range (j+1), if key i = key j then width i else 0 := by
  induction j with
  | zero => simp [segmentTotal]
  | succ j ih =>
    rw [segmentTotal, Finset.sum_range_succ, ite_eq_left rfl]
    by_cases he : key (j+1) = key j
    · rw [ite_eq_left he, he, ih (fun i l hil hlj => sorted i l hil (by omega)), Nat.add_comm]
    · rw [ite_eq_right he, Nat.add_zero, Finset.sum_eq_zero, Nat.zero_add]
      intro i hi
      have hi' : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hs := sorted i j hi' (Nat.le_succ _)
      have ht := sorted j (j+1) (Nat.le_succ _) le_rfl
      exact ite_eq_right (by omega)

/-- Exclusive offset of a row inside the sorted bucket with its key. -/
theorem total_sub_eq_sum (key width : ℕ → ℕ) (j : ℕ)
    (sorted : ∀ i l, i ≤ l → l ≤ j → key i ≤ key l) :
    segmentTotal key width j - width j = ∑ i ∈ Finset.range j, if key i = key j then width i else 0 := by
  rw [total_eq_sum key width j sorted, Finset.sum_range_succ, ite_eq_left rfl, Nat.add_sub_cancel]

end PackedScan

end BorderVNP
end Computability
end OAI

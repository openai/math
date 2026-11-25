import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic

/-! The blocks of synchronized short transforms in the integer algorithm. Each
block consists of four consecutive axes, with up to three leftover axes added
to the last block. It has enough spectator fibers for borrowing. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace SynchronizedBlocks

open Finset

/-- All but the last block have four axes. -/
def count {d : ℕ} (j : Fin (d / 4)) : ℕ :=
  if j.val + 1 = d / 4 then 4 + d % 4 else 4

theorem count_bounds {d : ℕ} (j : Fin (d / 4)) : 4 ≤ count j ∧ count j ≤ 7 := by
  unfold count
  split <;> omega

/-- Axis number in the original order. -/
def axis {d : ℕ} (j : Fin (d / 4)) (i : Fin (count j)) : Fin d :=
  ⟨4 * j.val + i.val, by
    have hj := j.isLt
    have hi := i.isLt
    unfold count at hi
    split at hi <;> omega⟩

/-- Block containing a specified axis. -/
def block {d : ℕ} (hd : 4 ≤ d) (a : Fin d) : Fin (d / 4) :=
  ⟨min (a.val / 4) (d / 4 - 1), by omega⟩

theorem block_axis {d : ℕ} (hd : 4 ≤ d) (j : Fin (d / 4)) (i : Fin (count j)) :
    block hd (axis j i) = j := by
  apply Fin.ext
  change min ((4 * j.val + i.val) / 4) (d / 4 - 1) = j.val
  have hj := j.isLt
  have hi := i.isLt
  unfold count at hi
  split at hi <;> omega

/-- The original axis order is a disjoint concatenation of the blocks. -/
def coordinates {d : ℕ} (hd : 4 ≤ d) : (Σ j : Fin (d / 4), Fin (count j)) ≃ Fin d where
  toFun x := axis x.1 x.2
  invFun a := ⟨block hd a, ⟨a.val - 4 * (block hd a).val, by
    have ha := a.isLt
    by_cases h : (block hd a).val + 1 = d / 4
    · rw [count, ite_eq_left h]
      simp only [block] at *
      omega
    · rw [count, ite_eq_right h]
      simp only [block] at *
      omega⟩⟩
  left_inv := by
    rintro ⟨j,i⟩
    apply Sigma.ext (block_axis hd j i)
    apply (Fin.heq_ext_iff (congrArg count (block_axis hd j i))).mpr
    change (axis j i).val - 4 * (block hd (axis j i)).val = i.val
    rw [block_axis]
    simp [axis]
  right_inv a := by
    apply Fin.ext
    change 4 * (block hd a).val + (a.val - 4 * (block hd a).val) = a.val
    simp only [block]
    omega

/-- The width of a whole block stays within seven maximum axis widths. -/
theorem bitWidth_le {d L : ℕ} (w : Fin d → ℕ) (hw : ∀ i, w i ≤ L)
    (j : Fin (d / 4)) : ∑ i : Fin (count j), w (axis j i) ≤ 7 * L := by
  calc
    _ ≤ ∑ _i : Fin (count j), L := sum_le_sum fun i _ ↦ hw _
    _ = count j * L := by simp
    _ ≤ 7 * L := Nat.mul_le_mul_right _ (count_bounds j).2

/-- The padded spectator ranges of each active axis provide at least eight
independent fibers. -/
theorem spectatorFibers_ge_eight {d : ℕ} (w : Fin d → ℕ) (hw : ∀ i, 0 < w i)
    (j : Fin (d / 4)) (i : Fin (count j)) :
    8 ≤ ∏ t ∈ univ.erase i, 2 ^ w (axis j t) := by
  classical
  have ht : 3 ≤ (univ.erase i).card := by
    rw [card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin]
    have := (count_bounds j).1
    omega
  calc
    8 = 2 ^ 3 := by decide
    _ ≤ 2 ^ (univ.erase i).card := Nat.pow_le_pow_right (by decide) ht
    _ = ∏ _t ∈ univ.erase i, 2 := by simp
    _ ≤ _ := prod_le_prod fun t _ ↦ by
      simpa using Nat.pow_le_pow_right (n := 2) (by decide) (hw (axis j t))

end SynchronizedBlocks

end NearSquareRoot
end Computability
end OAI

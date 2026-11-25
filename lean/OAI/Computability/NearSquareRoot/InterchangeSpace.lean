import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Space accounting on the active interchange path

The top frame holds its current array. A parked frame may keep arrays if the
child's stream has at most two thirds of the parent's volume; the reserve calls
on the full stream keep only a descriptor. Every descent reduces field width.
These facts suffice even with arbitrarily many full-volume calls on a path.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

theorem interchange_log_square_le (V : ℕ) (hV : V ≠ 0) :
    (Nat.log 2 V + 1) ^ 2 ≤ 4 * V := by
  suffices h : ∀ k : ℕ, (k + 1) ^ 2 ≤ 4 * 2 ^ k from
    (h _).trans (Nat.mul_le_mul_left _ (Nat.pow_log_le_self _ hV))
  intro k
  induction k with
  | zero => decide
  | succ k ih =>
    rcases k with _ | _ | k
    · decide
    · decide
    · rw [pow_succ 2]
      calc
        _ ≤ (k + 4) ^ 2 + (k ^ 2 + 4 * k + 2) := Nat.le_add_right _ _
        _ = 2 * (k + 3) ^ 2 := by ring
        _ ≤ 2 * (4 * 2 ^ (k + 2)) := Nat.mul_le_mul_left _ ih
        _ = _ := by ring

/-- Sum all arrays and descriptors on the path from depth zero to the active
node. `park i` counts the live array cells in the parked frame `i`. The
descriptor allowance is `B` times the bit length of the volume at the root.
The final term counts work space at the active node. -/
theorem interchange_path_space_bound (A B depth : ℕ)
    (volume width park : ℕ → ℕ)
    (hvol : ∀ i < depth, volume (i + 1) ≤ volume i)
    (hpark : ∀ i < depth, park i ≤ A * volume i)
    (hshrink : ∀ i < depth, park i = 0 ∨ 3 * volume (i + 1) ≤ 2 * volume i)
    (hwidth : ∀ i < depth, width (i + 1) < width i)
    (hroot : 2 ^ width 0 ≤ volume 0) :
    (∑ i ∈ Finset.range depth, park i) +
        depth * (B * (Nat.log 2 (volume 0) + 1)) + A * volume depth ≤
      (3 * A + 4 * B) * volume 0 := by
  have hV : volume 0 ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le (Nat.pow_pos (by decide)) hroot)
  have hsum : ∀ d ≤ depth,
      (∑ i ∈ Finset.range d, park i) + 3 * A * volume d ≤ 3 * A * volume 0 ∧
      d + width d ≤ width 0 := by
    intro d
    induction d with
    | zero => simp
    | succ d ih =>
      intro hd
      obtain ⟨hv, hw⟩ := ih (by omega)
      have hd' : d < depth := hd
      have hstep : park d + 3 * A * volume (d + 1) ≤ 3 * A * volume d := by
        rcases hshrink d hd' with he | he
        · rw [he, zero_add]
          exact Nat.mul_le_mul_left _ (hvol d hd')
        · have := Nat.mul_le_mul_left A he
          nlinarith [hpark d hd']
      rw [Finset.sum_range_succ]
      exact ⟨by omega, by have := hwidth d hd'; omega⟩
  obtain ⟨harrays, hdepth⟩ := hsum depth le_rfl
  have hwlog : width 0 ≤ Nat.log 2 (volume 0) :=
    (Nat.le_log_iff_pow_le (by decide) hV).mpr hroot
  have hdlog : depth ≤ Nat.log 2 (volume 0) + 1 := by omega
  have hdesc : depth * (B * (Nat.log 2 (volume 0) + 1)) ≤ 4 * B * volume 0 := calc
    _ ≤ (Nat.log 2 (volume 0) + 1) * (B * (Nat.log 2 (volume 0) + 1)) :=
      Nat.mul_le_mul_right _ hdlog
    _ = B * (Nat.log 2 (volume 0) + 1) ^ 2 := by ring
    _ ≤ B * (4 * volume 0) := Nat.mul_le_mul_left _ (interchange_log_square_le _ hV)
    _ = _ := by ring
  rw [Nat.add_mul]
  nlinarith

end NearSquareRoot
end Computability
end OAI

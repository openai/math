import Mathlib.Data.Nat.Log

namespace OAI
/-! # Integer halving thresholds in a heavy path of a formula -/

namespace Hierarchy.FormulaPartition

def threshold (d j : ℕ) : ℕ := d / 2 ^ j

@[simp] theorem threshold_zero (d : ℕ) : threshold d 0 = d := by
  simp [threshold]

theorem threshold_succ (d j : ℕ) : threshold d (j + 1) = threshold d j / 2 := by
  simp only [threshold, Nat.pow_succ, Nat.div_div_eq_div_mul]

theorem threshold_pos {d j : ℕ} (hd : 0 < d) (hj : j ≤ Nat.log 2 d) :
    0 < threshold d j :=
  Nat.div_pos (Nat.pow_le_of_le_log hd.ne' hj) (Nat.two_pow_pos j)

theorem threshold_log {d : ℕ} (hd : 0 < d) : threshold d (Nat.log 2 d) = 1 := by
  have lo := threshold_pos hd (le_refl (Nat.log 2 d))
  have hi : threshold d (Nat.log 2 d) < 2 := by
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2
    simpa only [Nat.pow_succ, Nat.mul_comm 2] using
      (Nat.lt_pow_of_log_lt (b := 2) (y := d) (by decide) (Nat.lt_succ_self _))
  omega

/-- A child carrying at least half of its parent clears the next threshold
whenever the parent clears the current one. -/
theorem threshold_lt_child {d j old child : ℕ}
    (greater : threshold d (j + 1) < old) (heavy : old ≤ 2 * child) :
    threshold d (j + 2) < child := by
  rw [threshold_succ d (j+1)]
  omega

end Hierarchy.FormulaPartition

end OAI

import Mathlib.Data.Nat.Log

/-!
# Cost of computing the ceiling binary logarithm on a unary tape

Each round pairs the remaining marks, keeps a mark for an unpaired last one,
outputs `B` marks, and transfers the shortened tally for the next round.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.CeilLog

theorem clog_step {n : ℕ} (hn : 2 ≤ n) :
    Nat.clog 2 n = Nat.clog 2 ((n + 1) / 2) + 1 := by
  simpa using Nat.clog_of_two_le (by decide : 1 < 2) hn

/-- Count the unary scan, pair emission, fixed output and return transfer. -/
def roundCost (B n : ℕ) : ℕ := n + 3 * ((n + 1) / 2) + B + 3

/-- The stopping tests take one instruction on an empty tally and two on a singleton. -/
def cost (B n : ℕ) : ℕ :=
  if _h : 2 ≤ n then roundCost B n + cost B ((n + 1) / 2) else n + 1
termination_by n
decreasing_by omega

@[simp] theorem cost_zero (B : ℕ) : cost B 0 = 1 := by rw [cost, dite_eq_right (by decide)]

@[simp] theorem cost_one (B : ℕ) : cost B 1 = 2 := by rw [cost, dite_eq_right (by decide)]

theorem cost_step (B : ℕ) {n : ℕ} (hn : 2 ≤ n) :
    cost B n = roundCost B n + cost B ((n + 1) / 2) := by
  rw [cost, dite_eq_left hn]

/-- For fixed output width the total instruction count is linear in the initial tally. -/
theorem cost_le (B n : ℕ) : cost B n ≤ (B + 32) * (n + 1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : 2 ≤ n
    · have hhalf : (n + 1) / 2 < n := by omega
      have hB : B * ((n + 1) / 2 + 1) + B ≤ B * (n + 1) := by
        rw [← Nat.mul_succ]
        exact Nat.mul_le_mul_left B (by omega)
      rw [cost_step B hn]
      calc
        _ ≤ roundCost B n + (B + 32) * ((n + 1) / 2 + 1) :=
          Nat.add_le_add_left (ih _ hhalf) _
        _ ≤ (B + 32) * (n + 1) := by simp only [roundCost, Nat.add_mul]; omega
    · rw [cost, dite_eq_right hn]
      exact Nat.le_mul_of_pos_left _ (by omega)

end RAMTape.CeilLog

end VPVNP
end Computability
end OAI

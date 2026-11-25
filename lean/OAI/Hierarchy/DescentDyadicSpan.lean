import Mathlib.Data.Nat.Log
import Mathlib.Tactic

namespace OAI
namespace Hierarchy.DescentDyadicSpan

def span (n : ℕ) : ℕ := 2 ^ Nat.clog 2 n

theorem span_pos (n : ℕ) : 0 < span n := Nat.two_pow_pos _
theorem span_ge (n : ℕ) : n ≤ span n := Nat.le_pow_clog (by decide) n

theorem span_le (n : ℕ) : span n ≤ 2*n+1 := by
  by_cases small : n ≤ 1
  · simp [span,Nat.clog_of_right_le_one small]
  · let d := Nat.clog 2 n
    have pos : 0 < d := Nat.clog_pos (by decide) (by omega)
    have h : 2^(d-1) < n := Nat.pow_pred_clog_lt_self (by decide) (by omega)
    change 2^d ≤ _
    calc
      2^d = 2^(d-1)*2 := by rw [← pow_succ]; congr 1; omega
      _ ≤ _ := by omega

end Hierarchy.DescentDyadicSpan

end OAI

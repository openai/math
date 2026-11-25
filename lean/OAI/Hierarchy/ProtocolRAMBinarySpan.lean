import Mathlib.Data.Nat.Log

namespace OAI
/-! # Power-of-two capacities for finite RAM columns -/

namespace Hierarchy.ProtocolRAMPurchaseSampler

def bits (k : ℕ) := Nat.log 2 (k+1)+1
def span (k : ℕ) := 2^bits k

theorem lt_span (k : ℕ) : k<span k :=
  (Nat.lt_succ_self _).trans (Nat.lt_pow_succ_log_self (by decide) _)

theorem span_le (k : ℕ) : span k ≤ 2*(k+1) := by
  change 2^(Nat.log 2 (k+1)+1) ≤ 2*(k+1)
  rw [Nat.pow_succ,Nat.mul_comm 2 (k+1)]
  exact Nat.mul_le_mul_right 2 (Nat.pow_log_le_self 2 (Nat.succ_ne_zero k))

end Hierarchy.ProtocolRAMPurchaseSampler

end OAI

import Mathlib.Data.Nat.Log
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-!
# Parameters for the densely occupied coprime box

The address has `k` bits. Take axes of width `20 * ⌈log₂ k⌉` and use the remaining
bits for a final binary axis. The interval of length `span k / k ^ 2` below each
full axis ceiling eventually contains any prescribed constant times `(k+1)²` cells.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace BoxScale

def width (k : ℕ) : ℕ := 20 * Nat.clog 2 k

def span (k : ℕ) : ℕ := 2 ^ width k

def count (k : ℕ) : ℕ := k / width k

theorem width_pos {k : ℕ} (hk : 1 < k) : 0 < width k :=
  Nat.mul_pos (by decide) (Nat.clog_pos (by decide) hk)

theorem count_mul_le (k : ℕ) : count k * width k ≤ k :=
  Nat.div_mul_le_self _ _

theorem count_le (k : ℕ) : count k ≤ k := Nat.div_le_self ..

theorem total_width (k : ℕ) : count k * width k + k % width k = k := by
  rw [Nat.mul_comm]
  exact Nat.div_add_mod ..

theorem remainder_lt {k : ℕ} (hk : 1 < k) : k % width k < width k :=
  Nat.mod_lt _ (width_pos hk)

theorem span_eq (k : ℕ) : span k = (2 ^ Nat.clog 2 k) ^ 20 := by
  unfold span width
  rw [Nat.mul_comm, Nat.pow_mul]

theorem pow_le_span (k : ℕ) : k ^ 20 ≤ span k := by
  rw [span_eq]
  exact Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) k) 20

theorem span_le {k : ℕ} (hk : 1 < k) : span k ≤ (2 * k) ^ 20 := by
  rw [span_eq]
  apply Nat.pow_le_pow_left
  have h := Nat.pow_pred_clog_lt_self (b := 2) (by decide) hk
  have hpos := Nat.clog_pos (b := 2) (by decide) hk
  have he : Nat.clog 2 k = (Nat.clog 2 k).pred + 1 := by simp only [Nat.pred_eq_sub_one]; omega
  calc
    2 ^ Nat.clog 2 k = 2 ^ ((Nat.clog 2 k).pred + 1) := congrArg (2 ^ ·) he
    _ = 2 * 2 ^ (Nat.clog 2 k).pred := by rw [Nat.pow_succ, Nat.mul_comm]
    _ ≤ 2 * k := Nat.mul_le_mul_left _ h.le

/-- Enough room below the padded ceiling for the quadratic Jacobsthal bound. -/
theorem room (C : ℕ) {k : ℕ} (hk : max 2 (4 * C) ≤ k) :
    C * (k + 1) ^ 2 ≤ span k / k ^ 2 := by
  have hk2 : 2 ≤ k := (le_max_left ..).trans hk
  have hC : 4 * C ≤ k := (le_max_right ..).trans hk
  apply (Nat.le_div_iff_mul_le (Nat.pow_pos (by omega) (n := 2))).2
  calc
    C * (k + 1) ^ 2 * k ^ 2 ≤ C * (2 * k) ^ 2 * k ^ 2 := by gcongr; omega
    _ = (4 * C) * k ^ 4 := by ring
    _ ≤ k * k ^ 4 := Nat.mul_le_mul_right _ hC
    _ = k ^ 5 := by ring
    _ ≤ k ^ 20 := Nat.pow_le_pow_right (by omega) (by decide)
    _ ≤ span k := pow_le_span _

private theorem twenty_mul_succ_le_pow {a : ℕ} (ha : 8 ≤ a) : 20 * (a+1) ≤ 2^a := by
  induction a, ha using Nat.le_induction with
  | base => decide
  | succ a ha ih => rw [Nat.pow_succ]; omega

theorem width_le {k : ℕ} (hk : 256 ≤ k) : width k ≤ k := by
  have hk2 : 1 < k := by omega
  have h := Nat.pow_pred_clog_lt_self (b := 2) (by decide) hk2
  unfold width
  by_cases hsmall : Nat.clog 2 k ≤ 8
  · omega
  · have hlarge : 8 ≤ (Nat.clog 2 k).pred := by simp only [Nat.pred_eq_sub_one]; omega
    have h' := twenty_mul_succ_le_pow hlarge
    simp only [Nat.pred_eq_sub_one] at h' h
    omega

end BoxScale

end NearSquareRoot
end Computability
end OAI

import OAI.Computability.NearSquareRoot.Asymptotic

/-! # Time and scratch radius for a short-word call -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortWord

/-- Clock for one call on a pair of positive, equal-width words. -/
def clock (k : ℕ) : ℕ := k * max 1 (Nat.clog 2 k)

theorem clock_le_log {k : ℕ} (hk : 0 < k) :
    (clock k : ℝ) ≤ k * ((1 + (Real.log 2)⁻¹) * (1 + Real.log k)) := by
  rw [clock, Nat.cast_mul]
  exact mul_le_mul_of_nonneg_left (clog_le_logScale hk) (Nat.cast_nonneg k)

/-- A fixed multiple of the address width costs only a fixed multiple of its clock. -/
theorem clock_scale {w W k : ℕ} (hw : w ≤ W*k) :
    clock w ≤ (W * (Nat.clog 2 W + 1)) * clock k := by
  have hlog : Nat.clog 2 w ≤ Nat.clog 2 W + Nat.clog 2 k := by
    apply Nat.clog_le_of_le_pow
    rw [Nat.pow_add]
    exact hw.trans (Nat.mul_le_mul (Nat.le_pow_clog (by decide) W) (Nat.le_pow_clog (by decide) k))
  let β := max 1 (Nat.clog 2 k)
  have hk : 1 ≤ β := Nat.le_max_left ..
  have hk' : Nat.clog 2 k ≤ β := Nat.le_max_right ..
  have hW := Nat.le_mul_of_pos_right (Nat.clog 2 W) hk
  have hb : max 1 (Nat.clog 2 w) ≤ (Nat.clog 2 W + 1)*β := by
    rw [Nat.add_mul, Nat.one_mul]
    omega
  calc
    clock w ≤ (W*k)*((Nat.clog 2 W+1)*β) := Nat.mul_le_mul hw hb
    _ = (W*(Nat.clog 2 W+1))*clock k := by unfold clock; dsimp [β]; ring

private theorem square_le_two_pow (k : ℕ) (hk : 4 ≤ k) : k^2 ≤ 2^k := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    rw [pow_succ (2 : ℕ) k]
    nlinarith [Nat.mul_le_mul_left k hk]

/-- A short-word call with fixed multiplicative constants fits inside one full array's
space budget once its address width passes the indicated constant threshold.
The running-time clock bounds the distance of every scratch head. -/
theorem callFitsArray (C W k w : ℕ) (h : max 4 (C*((W+1)^2+1)) ≤ k) (hw : w ≤ W*k) :
    C * (clock w + 1) ≤ 2^k * k := by
  have hk := (le_max_left ..).trans h
  have hC := (le_max_right ..).trans h
  have hc : Nat.clog 2 w ≤ w := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self.le)
  have hh : max 1 (Nat.clog 2 w) ≤ w+1 := max_le (by omega) (by omega)
  have h1 : w + 1 ≤ (W+1)*k := by rw [Nat.add_mul, Nat.one_mul]; omega
  calc
    C * (clock w + 1) ≤ C * (((W+1)*k)^2 + 1) := by
      unfold clock
      gcongr
      rw [pow_two]
      exact Nat.mul_le_mul ((Nat.le_succ w).trans h1) (hh.trans h1)
    _ ≤ C * (((W+1)^2+1)*k^2) := by
      rw [Nat.mul_pow, Nat.add_mul, Nat.one_mul]
      gcongr
      exact Nat.pow_pos (by omega)
    _ = (C*((W+1)^2+1))*k^2 := (Nat.mul_assoc ..).symm
    _ ≤ k*k^2 := Nat.mul_le_mul_right _ hC
    _ ≤ 2^k*k := by rw [Nat.mul_comm (2^k) k]; exact Nat.mul_le_mul_left _ (square_le_two_pow k hk)

/-- For a full array of records, the two stream lengths and the reusable scratch
radius fit in a constant multiple of the array volume. The multiplicative constant
does not depend on the hidden constant in the local time bound. -/
theorem batchFitsArray (C W k w : ℕ) (h : max 4 (C*((W+1)^2+1)) ≤ k) (hw : w ≤ W*k) :
    2^k*(2*w+2) + 2*(C*(clock w+1)) + 1 ≤ (2*W+5)*(2^k*k) := by
  have hk := (le_max_left ..).trans h
  have ha : 2*w+2 ≤ (2*W+2)*k := by
    rw [Nat.add_mul, Nat.mul_assoc]
    omega
  have hscan : 2^k*(2*w+2) ≤ (2*W+2)*(2^k*k) := calc
    _ ≤ 2^k*((2*W+2)*k) := Nat.mul_le_mul_left _ ha
    _ = _ := by ring
  have hclock := callFitsArray C W k w h hw
  have hvol : 1 ≤ 2^k*k := Nat.mul_pos (by positivity) (by omega)
  have hx : (2*W+5)*(2^k*k) = (2*W+2)*(2^k*k)+3*(2^k*k) := by ring
  omega

end ShortWord

end NearSquareRoot
end Computability
end OAI

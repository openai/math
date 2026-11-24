import OAI.Computability.VPVNP.RAMParameters

/-!
# Integer operands for the virtual site count

Section 11 chooses the least power of two whose buckets cover the probe budget.
Its address width can be computed from the live address width and the product of
the input length with its ceiling logarithm. This computation keeps the live
processor count in exponent form and fits in the prescribed machine words.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace BurstRAM

private theorem clog_two_pow_mul (r m : ℕ) (hm : 0 < m) :
    Nat.clog 2 (2 ^ r * m) = r + Nat.clog 2 m := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hp : 0 < 2 ^ r * m := Nat.mul_pos (Nat.two_pow_pos _) hm
    rw [pow_succ, Nat.mul_right_comm, Nat.clog_of_two_le (by decide : 1 < 2) (by omega)]
    rw [show (2 ^ r * m * 2 + 2 - 1) / 2 = 2 ^ r * m by omega, ih]
    omega

/-- The virtual address width, computed without forming the live processor count. -/
theorem virtualSiteExponent_eq_add_sub (r n : ℕ) (hn : 2 ≤ n) :
    virtualSiteExponent r n =
      r + Nat.clog 2 (n * Nat.clog 2 n) - (Nat.clog 2 n + 3) / 4 := by
  have hc := Nat.clog_pos (by decide : 1 < 2) hn
  rw [virtualSiteExponent, Nat.mul_assoc, clog_two_pow_mul _ _ (Nat.mul_pos (by omega) hc),
    roundedUp, pow_one, Nat.clog_pow_left]

/-- The product whose logarithm supplies the extra address bits has at most
twice the ceiling logarithm of the input length as its ceiling logarithm. -/
theorem clog_length_mul_clog_le (n : ℕ) :
    Nat.clog 2 (n * Nat.clog 2 n) ≤ 2 * Nat.clog 2 n := by
  let c := Nat.clog 2 n
  apply Nat.clog_le_of_le_pow
  calc
    n * c ≤ 2 ^ c * 2 ^ c := Nat.mul_le_mul (Nat.le_pow_clog Nat.one_lt_two _) Nat.lt_two_pow_self.le
    _ = 2 ^ (2 * c) := by rw [← pow_add, two_mul]

/-- At every input length the product and its increment, the sum of the two
logarithmic counters, and the numerator for ceiling division by four fit in a
live processor word. -/
theorem virtualParameterOperands_lt {B : ℕ} (hB : 1 ≤ B) (n : ℕ) :
    let r := addressWidth B n
    let w := (r + 10) ^ 4
    let c := Nat.clog 2 n
    n * c + 1 < 2 ^ w ∧ r + Nat.clog 2 (n * c) < 2 ^ w ∧ c + 3 < 2 ^ w := by
  let r := addressWidth B n
  let w := (r + 10) ^ 4
  let c := Nat.clog 2 n
  have hcr : c ≤ r := Nat.le_mul_of_pos_left _ hB
  have hw : 3 * r + 4 ≤ w := by
    change 3 * r + 4 ≤ (r + 10) ^ 4
    calc
      _ ≤ (r + 10) ^ 2 := by nlinarith [Nat.zero_le (r * r)]
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by decide : 2 ≤ 4)
  have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 * c + 2 ≤ w by omega)
  have hprod : n * c ≤ 2 ^ (2 * c) :=
    (Nat.le_pow_clog Nat.one_lt_two _).trans
      (Nat.pow_le_pow_right (by decide) (clog_length_mul_clog_le n))
  have hmargin : 0 < 2 ^ (2 * c) := Nat.two_pow_pos _
  rw [pow_add] at hpow
  have hcount := clog_length_mul_clog_le n
  change Nat.clog 2 (n * c) ≤ 2 * c at hcount
  have hlarge : w < 2 ^ w := Nat.lt_two_pow_self
  change n * c + 1 < 2 ^ w ∧ r + Nat.clog 2 (n * c) < 2 ^ w ∧ c + 3 < 2 ^ w
  constructor
  · norm_num1 at hpow
    omega
  · omega

end BurstRAM

end VPVNP
end Computability
end OAI

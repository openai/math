import Mathlib.Tactic

/-!
# Parameter bounds for broadcasting a shared label

For the qualitative sunflower theorem, the broadcast slope may exceed one by
any prescribed positive amount.  Fix the box dimension `h + 6` in advance,
then increase its side length with the number of bits.  This gives slope
`1 + 6 / h` with an additive constant independent of the alphabet.
-/

namespace OAI
namespace Combinatorics
namespace Sunflower
namespace BroadcastParameters

/-- The dimension of the integer box. Six coordinates pay for two pigeonhole losses. -/
def dim (h : ℕ) : ℕ := h + 6

/-- Bit depth of each coordinate. -/
def depth (h b : ℕ) : ℕ := b / h + dim h + 2

def side (h b : ℕ) : ℕ := 2 ^ depth h b

/-- Every coordinate of either side of the broadcast relation lies below this modulus. -/
def modulus (h b sites : ℕ) : ℕ := 2 ^ (depth h b + sites)

def bits (h b sites : ℕ) : ℕ := (depth h b + sites) * dim h

theorem modulus_pos (h b sites : ℕ) : 0 < modulus h b sites := by
  unfold modulus
  positivity

theorem side_pos (h b : ℕ) : 0 < side h b := by
  unfold side
  positivity

theorem modulus_pow_dim (h b sites : ℕ) :
    modulus h b sites ^ dim h = 2 ^ bits h b sites := by
  rw [modulus, bits, pow_mul]

theorem no_wrap (h b sites : ℕ) :
    sites * (side h b - 1) < modulus h b sites := by
  rw [modulus, pow_add, mul_comm (2 ^ depth h b)]
  exact lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.sub_le (side h b) 1))
    (Nat.mul_lt_mul_of_pos_right (Nat.lt_two_pow_self (n := sites)) (side_pos h b))

private theorem box_bucket_bound (h b : ℕ) :
    1 + dim h * (side h b - 1)^2 ≤ (side h b)^3 := by
  let m := dim h
  let q := side h b
  have hmq : m + 1 ≤ q := by
    have hmd : m ≤ depth h b :=
      (Nat.le_add_left m (b / h)).trans (Nat.le_add_right _ 2)
    have hd := Nat.lt_two_pow_self (n := depth h b)
    exact Nat.succ_le_of_lt (lt_of_le_of_lt hmd hd)
  have hq : 0 < q := side_pos h b
  have sq : 1 ≤ q^2 := Nat.succ_le_of_lt (pow_pos hq 2)
  calc
    1 + m * (q - 1)^2 ≤ q^2 + m * q^2 := by
      gcongr
      exact Nat.sub_le _ _
    _ = (m + 1) * q^2 := by ring
    _ ≤ q * q^2 := Nat.mul_le_mul_right _ hmq
    _ = q^3 := by ring

theorem code_capacity {h : ℕ} (hh : 0 < h) (b : ℕ) :
    (1 + dim h * (side h b - 1)^2)^2 * 2^b ≤ side h b ^ dim h := by
  have hb : b ≤ depth h b * h := by
    have hr := Nat.mod_lt b hh
    have hdiv := Nat.div_add_mod b h
    unfold depth
    rw [Nat.add_mul, Nat.add_mul, mul_comm (b / h)]
    omega
  have hcap : 2^b ≤ side h b ^ h := by
    rw [side, ← pow_mul]
    exact Nat.pow_le_pow_right (by decide) hb
  calc
    _ ≤ ((side h b)^3)^2 * side h b ^ h := by
      gcongr
      exact box_bucket_bound h b
    _ = side h b ^ (h + 6) := by rw [← pow_mul, pow_add, mul_comm]

/-- A size bound on the exponent of the diagonal resource. The overhead is
independent of the bit length once the slope parameter and sites are fixed. -/
theorem bits_le {h : ℕ} (hh : 0 < h) (b sites : ℕ) :
    (bits h b sites : ℝ) ≤ (1 + 6 / (h : ℝ)) * b +
      (dim h : ℝ) * ((dim h : ℝ) + 2 + sites) := by
  have hh' : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
  have hdiv : ((b / h : ℕ) : ℝ) ≤ b / h := Nat.cast_div_le
  unfold bits depth
  push_cast
  calc
    _ ≤ ((b : ℝ) / h + dim h + 2 + sites) * dim h := by gcongr
    _ = _ := by
      unfold dim
      push_cast
      field_simp
      ring

end BroadcastParameters
end Sunflower
end Combinatorics
end OAI

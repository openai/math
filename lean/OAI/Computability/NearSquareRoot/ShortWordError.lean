import OAI.Computability.IntegerMultiplication.Goal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Truncation of a sign-magnitude fixed-point product toward zero. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortWord.FixedPoint

open IntegerMultiplication

private theorem bitValue_append_bit (w : List Bool) (b : Bool) :
    bitValue (w ++ [b]) = 2 * bitValue w + b.toNat := by
  simp [bitValue, List.foldl_append]

/-- Removing low bits from an MSF magnitude divides its decoded value by a power of two.
This includes words with leading zeros and shifts exceeding the word length. -/
theorem bitValue_drop_low (w : List Bool) (p : ℕ) :
    bitValue (w.reverse.drop p).reverse = bitValue w / 2^p := by
  suffices h : ∀ (l : List Bool), bitValue (l.drop p).reverse = bitValue l.reverse / 2^p by
    simpa using h w.reverse
  induction p with
  | zero => simp
  | succ p ih =>
    intro l
    cases l with
    | nil => simp [bitValue]
    | cons b l =>
      simp only [List.drop_succ_cons, ih, List.reverse_cons, bitValue_append_bit]
      rw [pow_succ', ← Nat.div_div_eq_div_mul]
      congr 1
      cases b <;> simp
      omega

/-- A sign bit set to true denotes a negative magnitude. The binary point is located
`p` bits to the left of the low end of the word. -/
noncomputable def signedDyadic (s : Bool) (x p : ℕ) : ℝ :=
  if s then -((x : ℝ) / 2 ^ p) else (x : ℝ) / 2 ^ p

private theorem unsignedDyadic_mul_error (x y p : ℕ) :
    |((x*y / 2^p : ℕ) : ℝ) / 2^p - (x : ℝ) / 2^p * ((y : ℝ) / 2^p)| <
      1 / (2 : ℝ)^p := by
  let d : ℕ := 2^p
  have hd : 0 < d := Nat.pow_pos (by decide)
  have hd' : 0 < (d : ℝ) := by exact_mod_cast hd
  let r := x*y % d
  let q := x*y / d
  have hr : (r : ℝ) < d := by exact_mod_cast Nat.mod_lt (x*y) hd
  have he : (d : ℝ) * q + r = (x : ℝ) * y := by exact_mod_cast Nat.div_add_mod (x*y) d
  have hpow : (d : ℝ) = 2^p := by simp [d]
  change |(q : ℝ) / 2^p - (x : ℝ) / 2^p * ((y : ℝ) / 2^p)| < _
  rw [← hpow]
  have herr : (q : ℝ) / d - (x : ℝ) / d * ((y : ℝ) / d) = -((r : ℝ) / (d*d)) := by
    field_simp
    linarith
  rw [herr, abs_neg, abs_of_nonneg (by positivity)]
  rw [← div_div, div_lt_div_iff_of_pos_right hd', div_lt_iff₀ hd', one_mul]
  exact hr

/-- After multiplying full magnitudes and discarding the low `p` bits, the absolute
error is strictly less than one unit of the output grid, for every choice of signs. -/
theorem signedDyadic_mul_error (sx sy : Bool) (x y p : ℕ) :
    |signedDyadic (sx ^^ sy) (x*y / 2^p) p - signedDyadic sx x p * signedDyadic sy y p| <
      1 / (2 : ℝ)^p := by
  have h := unsignedDyadic_mul_error x y p
  cases sx <;> cases sy <;>
    simpa [signedDyadic, Bool.xor, neg_add_eq_sub, abs_sub_comm] using h

end ShortWord.FixedPoint

end NearSquareRoot
end Computability
end OAI

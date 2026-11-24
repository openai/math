import OAI.Computability.VPVNP.RAMTapeWordSlice
import OAI.Computability.VPVNP.RAMProgram

/-!
# Logical shifts on fixed-width bit tapes

A right shift drops the low bits and fills the high end with zeros. For a
left shift the tape is reversed before and after the same operation. The
number of zeros is capped at the width, so an overshift clears the tape.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace TapeWord.Shift

open BurstRAM

/-- Drop and fill in the orientation determined by the shift direction. -/
def result (left : Bool) (x : List Bool) (n : ℕ) : List Bool :=
  let z := if left then x.reverse else x
  let y := z.drop n ++ List.replicate (min n z.length) false
  if left then y.reverse else y

@[simp] theorem length_result (left : Bool) (x : List Bool) (n : ℕ) :
    (result left x n).length = x.length := by
  cases left <;> simp [result] <;> omega

private theorem value_drop {xs : List Bool} {n : ℕ} (hn : n ≤ xs.length) :
    value (xs.drop n) = value xs / 2 ^ n := by
  have hlen : (xs.take n).length = n := by simp [hn]
  have hlow : value (xs.take n) < 2 ^ n := by simpa only [hlen] using value_lt (xs.take n)
  have h := congrArg value (List.take_append_drop n xs)
  rw [value_append, hlen] at h
  rw [← h, Nat.add_mul_div_left _ _ (Nat.pow_pos (by decide)), Nat.div_eq_of_lt hlow, Nat.zero_add]

/-- The bit-string shift computes the RAM shift for every width and amount. -/
theorem result_wordBits {w : ℕ} (left : Bool) (x y : Word w) :
    result left (wordBits x) y.val =
      wordBits ((if left then PrivateRAM.BinaryOp.shiftLeft else .shiftRight).eval x y) := by
  apply eq_of_length_value
  · simp
  rw [value_wordBits]
  by_cases hn : y.val < w
  · have hlen : y.val ≤ (wordBits x).length := by simpa using hn.le
    cases left with
    | false =>
      have hsmall : x.val / 2 ^ y.val < 2 ^ w :=
        (Nat.div_le_self _ _).trans_lt x.isLt
      simp [result, value_append, value_drop hlen, value_wordBits, PrivateRAM.BinaryOp.eval,
        hn, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hsmall]
    | true =>
      have hpow : 2 ^ w = 2 ^ y.val * 2 ^ (w - y.val) := by
        rw [← pow_add, Nat.add_sub_of_le hn.le]
      simp [result, List.drop_reverse, value_append, value_take_mod, value_wordBits, hn.le,
        PrivateRAM.BinaryOp.eval, hn, Nat.shiftLeft_eq, Nat.mul_comm x.val, hpow,
        Nat.mul_mod_mul_left]
  · have hdrop : (wordBits x).length ≤ y.val := by simpa using Nat.le_of_not_gt hn
    have hrev : (wordBits x).reverse.length ≤ y.val := by simpa using hdrop
    cases left <;> simp [result, List.drop_of_length_le hdrop, List.drop_of_length_le hrev,
      PrivateRAM.BinaryOp.eval, hn]

end TapeWord.Shift

end VPVNP
end Computability
end OAI

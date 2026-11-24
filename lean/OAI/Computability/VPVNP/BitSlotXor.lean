import OAI.Computability.VPVNP.BitSlotIndex
import OAI.Computability.VPVNP.RAMProgram

/-!
# Binary tag arithmetic on the private RAM

Appendix C's greedy tag assignment uses the additive group of binary vectors.
With the slot numbering of `BitSlotIndex`, vector addition is one native XOR
instruction, including when the tag occupies only the low bits of a RAM word.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

private theorem xor_head_tail {n a b : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n)
    (i j : ℕ) :
    (a + 2 ^ n * i) ^^^ (b + 2 ^ n * j) = (a ^^^ b) + 2 ^ n * (i ^^^ j) := by
  rw [← Nat.mod_add_div ((a + 2 ^ n * i) ^^^ (b + 2 ^ n * j)) (2 ^ n)]
  simp only [Nat.xor_mod_two_pow, Nat.xor_div_two_pow, Nat.add_mul_mod_self_left,
    Nat.add_mul_div_left _ _ (Nat.two_pow_pos n), Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
    Nat.div_eq_of_lt ha, Nat.div_eq_of_lt hb, zero_add]

private theorem binary_digit_add (a b : ZMod 2) : (a + b).val = a.val ^^^ b.val := by
  decide +revert

/-- The binary numbering takes coordinatewise addition to XOR of the numbers. -/
theorem bitWordFinEquiv_add_val {j : ℕ} (x y : BitWord j) :
    (bitWordFinEquiv j (x + y)).val = (bitWordFinEquiv j x).val ^^^ (bitWordFinEquiv j y).val := by
  induction j with
  | zero =>
    change 0 = (0 : ℕ) ^^^ 0
    simp
  | succ j ih =>
    rw [bitWordFinEquiv_val, bitWordFinEquiv_val j x, bitWordFinEquiv_val j y,
      xor_head_tail (bitWordFinEquiv j (Fin.tail x)).isLt (bitWordFinEquiv j (Fin.tail y)).isLt]
    change (bitWordFinEquiv j (Fin.tail x + Fin.tail y)).val + 2 ^ j * (x 0 + y 0).val = _
    rw [ih, binary_digit_add]

variable {j w : ℕ}

/-- Store a binary tag in the low bits of a RAM word, zero-extending its number. -/
def tagWord (hw : j ≤ w) (x : BitWord j) : Word w :=
  Fin.castLE (Nat.pow_le_pow_right (by decide) hw) (bitWordFinEquiv j x)

@[simp] theorem tagWord_val (hw : j ≤ w) (x : BitWord j) :
    (tagWord hw x).val = (bitWordFinEquiv j x).val := rfl

theorem tagWord_injective (hw : j ≤ w) : Function.Injective (tagWord hw) :=
  (Fin.castLE_injective _).comp (bitWordFinEquiv j).injective

@[simp] theorem tagWord_zero (hw : j ≤ w) : tagWord hw 0 = 0 := by
  apply Fin.ext
  simpa using bitWordFinEquiv_add_val (0 : BitWord j) 0

@[simp] theorem tagWord_neg (hw : j ≤ w) (x : BitWord j) : tagWord hw (-x) = tagWord hw x := by
  congr 1
  exact funext fun i ↦ CharTwo.neg_eq (x i)

/-- Evaluating the native bitwise instruction computes tag addition exactly. -/
@[simp] theorem tagWord_xor (hw : j ≤ w) (x y : BitWord j) :
    BinaryOp.bitXor.eval (tagWord hw x) (tagWord hw y) = tagWord hw (x + y) := by
  apply Fin.ext
  simp only [BinaryOp.eval, Fin.val_ofNat, tagWord_val, bitWordFinEquiv_add_val]
  exact Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (tagWord hw x).isLt (tagWord hw y).isLt)

end Compression

end VPVNP
end Computability
end OAI

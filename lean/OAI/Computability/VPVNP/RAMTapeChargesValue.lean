import OAI.Computability.VPVNP.RAMTapeWordSlice

/-!
# Single-unit arithmetic for binary charge counters

A charge subtracts one from the remaining global budget and adds one to
the cumulative cost. The carry or borrow beyond the high bit detects every
overflow or underflow, including in a zero-width counter.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.Charges

open TapeWord BurstRAM

/-- Propagate a carry through a set bit when incrementing, or a borrow through a zero bit when
decrementing. -/
def nextCarry (up carry bit : Bool) : Bool := carry && (if up then bit else !bit)

/-- Ripple one incoming unit up or down across the little-endian bits. -/
def adjust (up carry : Bool) (bits : List Bool) : List Bool × Bool :=
  scan (if up then addBit else subBit) carry bits (List.replicate bits.length false)

@[simp] theorem adjust_nil (up carry : Bool) : adjust up carry [] = ([], carry) := rfl

theorem adjust_cons (up carry bit : Bool) (bits : List Bool) :
    adjust up carry (bit :: bits) =
      let t := adjust up (nextCarry up carry bit) bits
      ((bit ^^ carry) :: t.1, t.2) := by
  cases up <;> cases carry <;> cases bit <;> rfl

@[simp] theorem adjust_length (up carry : Bool) (bits : List Bool) :
    (adjust up carry bits).1.length = bits.length :=
  length_scan _ _ _ _ (by simp)

theorem adjust_up_spec (carry : Bool) (bits : List Bool) :
    value (adjust true carry bits).1 + 2 ^ bits.length * (adjust true carry bits).2.toNat =
      value bits + carry.toNat := by
  simpa only [adjust, ↓reduceIte, value_zeros, Nat.add_zero] using
    addScan_spec (c := carry) (x := bits) (y := List.replicate bits.length false) (by simp)

theorem adjust_down_spec (carry : Bool) (bits : List Bool) :
    value (adjust false carry bits).1 + carry.toNat =
      value bits + 2 ^ bits.length * (adjust false carry bits).2.toNat := by
  simpa only [adjust, Bool.false_eq_true, ↓reduceIte, value_zeros, Nat.add_zero] using
    subScan_spec (c := carry) (x := bits) (y := List.replicate bits.length false) (by simp)

theorem adjust_borrow_iff (bits : List Bool) :
    (adjust false true bits).2 = true ↔ value bits = 0 := by
  have h := adjust_down_spec true bits
  have hb := value_lt (adjust false true bits).1
  rw [adjust_length] at hb
  cases hflag : (adjust false true bits).2 <;>
    simp only [hflag, Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.add_zero, Nat.mul_one] at h <;>
    simp <;> omega

theorem adjust_overflow_iff (bits : List Bool) :
    (adjust true true bits).2 = true ↔ 2 ^ bits.length ≤ value bits + 1 := by
  have h := adjust_up_spec true bits
  have hb := value_lt (adjust true true bits).1
  rw [adjust_length] at hb
  cases hflag : (adjust true true bits).2 <;>
    simp only [hflag, Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.add_zero, Nat.mul_one] at h <;>
    simp <;> omega

variable {w : ℕ}

/-- The predecessor cost word. At zero the borrow flag rejects the charge. -/
def prevWord (x : Word w) : Word w := ⟨x.val - 1, (Nat.sub_le ..).trans_lt x.isLt⟩

theorem adjust_dec_word (x : Word w) (hx : 0 < x.val) :
    adjust false true (wordBits x) = (wordBits (prevWord x), false) := by
  have he := adjust_down_spec true (wordBits x)
  have hf : (adjust false true (wordBits x)).2 = false := by
    apply Bool.eq_false_iff.mpr
    intro hb
    have := (adjust_borrow_iff _).mp hb
    rw [value_wordBits] at this
    omega
  apply Prod.ext _ hf
  apply eq_of_length_value (by simp)
  simp only [hf, Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.add_zero, value_wordBits] at he
  rw [value_wordBits]
  change _ = x.val - 1
  omega

theorem adjust_inc_word (x : Word w) (hx : x.val + 1 < 2 ^ w) :
    adjust true true (wordBits x) = (wordBits (⟨x.val + 1, hx⟩ : Word w), false) := by
  have he := adjust_up_spec true (wordBits x)
  have hf : (adjust true true (wordBits x)).2 = false := by
    apply Bool.eq_false_iff.mpr
    intro hb
    have := (adjust_overflow_iff _).mp hb
    rw [value_wordBits, length_wordBits] at this
    omega
  apply Prod.ext _ hf
  apply eq_of_length_value (by simp)
  simpa [hf, value_wordBits] using he

end RAMTape.Charges

end VPVNP
end Computability
end OAI

import OAI.Computability.VPVNP.RAMTapeWordSlice

/-!
# Binary word increment for the unary input routine

Reading one unary mark adds one to a fixed-width little-endian word. The scan
keeps a single carry bit in finite control, including the carry out of the
highest bit. The input-length and unit words both fit the allocated width.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.UnaryWord

open BurstRAM TapeWord

/-- Add the incoming carry to a little-endian bit list and retain the overflow bit. -/
def incScan : Bool → List Bool → List Bool × Bool
  | carry, [] => ([], carry)
  | carry, b :: bits =>
    let (rest, final) := incScan (b && carry) bits
    ((b ^^ carry) :: rest, final)

theorem incScan_length (carry : Bool) (bits : List Bool) :
    (incScan carry bits).1.length = bits.length := by
  induction bits generalizing carry with
  | nil => rfl
  | cons b bits ih => simp [incScan, ih]

theorem incScan_value (carry : Bool) (bits : List Bool) :
    value (incScan carry bits).1 + 2 ^ bits.length * (incScan carry bits).2.toNat =
      value bits + carry.toNat := by
  induction bits generalizing carry with
  | nil => simp [incScan, value]
  | cons b bits ih =>
    have h := ih (b && carry)
    have hdigit : (b ^^ carry).toNat + 2 * (b && carry).toNat = b.toNat + carry.toNat := by
      cases b <;> cases carry <;> decide
    simp only [incScan, value, List.length_cons, pow_succ, Nat.mul_right_comm _ 2 _]
    omega

/-- If the increment fits in the allocated word, the result retains its full value. -/
theorem incScan_value_of_lt (carry : Bool) (bits : List Bool)
    (hfit : value bits + carry.toNat < 2 ^ bits.length) :
    value (incScan carry bits).1 = value bits + carry.toNat := by
  have h := incScan_value carry bits
  cases hc : (incScan carry bits).2 <;> simp [hc] at h <;> omega

theorem zeros_value (k : ℕ) : value (List.replicate k false) = 0 :=
  TapeWord.value_zeros k

/-- Allocated word width for a program parameter `p` and unary input length `n`. -/
def width (p n : ℕ) : ℕ := (p + 1) * (n + 1)

theorem width_pos (p n : ℕ) : 0 < width p n := Nat.mul_pos (by omega) (by omega)

/-- The encoded length fits even for a zero program parameter. -/
def inputWord (p n : ℕ) : Word (width p n) :=
  ⟨n, by
    have hn : n + 1 ≤ width p n := Nat.le_mul_of_pos_left _ (by omega)
    exact (Nat.lt_of_succ_le hn).trans (Nat.lt_pow_self (by decide))⟩

@[simp] theorem inputWord_val (p n : ℕ) : (inputWord p n).val = n := rfl

/-- The word one is available for every input, including the empty input. -/
def unitWord (p n : ℕ) : Word (width p n) :=
  ⟨1, lt_of_le_of_lt (width_pos p n) (Nat.lt_pow_self (by decide))⟩

@[simp] theorem unitWord_val (p n : ℕ) : (unitWord p n).val = 1 := rfl

theorem zeros_wordBits (w : ℕ) : List.replicate w false = wordBits (0 : Word w) :=
  eq_of_length_value (by simp) (by simp [value_wordBits])

theorem unit_wordBits (p n : ℕ) :
    true :: List.replicate (width p n - 1) false = wordBits (unitWord p n) := by
  apply eq_of_length_value
  · simp only [List.length_cons, List.length_replicate, length_wordBits]
    have := width_pos p n
    omega
  · simp [value, value_wordBits]

end RAMTape.UnaryWord

end VPVNP
end Computability
end OAI

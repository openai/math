import OAI.Computability.NearSquareRoot.PrecisionGrid

/-! # Exact digit records and the phase-stream seed -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedPoint

open IntegerMultiplication

/-- Nonnegative radix digit with the binary point shifted by the fractional width. -/
def digitRecord (k n : ℕ) : Record k :=
  Grid.wrapMap (componentBits k) ⟨(n * 2 ^ fractionBits k : ℕ), 0⟩

private theorem scaled_digit_lt {k n : ℕ} (h : n ≤ 2 ^ (13 * k)) :
    n * 2 ^ fractionBits k < 2 ^ componentBits k := by
  calc
    _ ≤ 2 ^ (13 * k) * 2 ^ fractionBits k := Nat.mul_le_mul_right _ h
    _ < _ := by
      rw [← pow_add]
      apply Nat.pow_lt_pow_right (by decide)
      unfold fractionBits componentBits
      omega

theorem value_digit {k n : ℕ} (h : n ≤ 2 ^ (13 * k)) :
    value k (digitRecord k n) = (n : ℂ) := by
  let a : Grid.Cell := ⟨(n * 2 ^ fractionBits k : ℕ), 0⟩
  have ha : Grid.focus (componentBits k) a := by
    change |((n * 2 ^ fractionBits k : ℕ) : ℤ)| < (2 : ℤ) ^ _ ∧ |(0 : ℤ)| < 2 ^ _
    rw [Int.abs_natCast, abs_zero]
    exact ⟨by exact_mod_cast scaled_digit_lt h, by positivity⟩
  change Grid.toC (Grid.aspect (Grid.wrapMap _ a)) / _ = _
  rw [Grid.recovers _ ha]
  simp [a, Grid.toC]

/-- A single framed digit initializer, with both widths carried by tape rulers.
The magnitude word is little endian as in the reversed input scan. -/
def encodeDigit (args : Bits.Word × Code.Tally × Code.Tally) : Dusk.Pair :=
  (Bits.resize (args.2.2, Code.fill false args.2.1 ++ args.1), Code.fill false args.2.2)

@[fun_prop]
theorem encodeDigit_easy : Code.Easy encodeDigit := by unfold encodeDigit; fun_prop

theorem encodeDigit_eq {k : ℕ} (xs : Bits.Word) (h : Bits.value xs ≤ 2 ^ (13 * k)) :
    encodeDigit (xs, Code.tally (fractionBits k), Code.tally (componentBits k + 1)) =
      Dusk.mark (digitRecord k (Bits.value xs)) := by
  let w := componentBits k
  let p := fractionBits k
  have hwidth : (2 : ℕ)^w ≤ Dusk.period w := by
    have e := Dusk.period_s w
    rw [pow_succ] at e
    have : 0 < (2 : ℕ)^w := by positivity
    omega
  have hmod : Bits.value xs * 2^p < Dusk.period w := (scaled_digit_lt h).trans_le hwidth
  have hd : ZMod.val (digitRecord k (Bits.value xs)).re = Bits.value xs * 2^p := by
    change ZMod.val ((↑((↑(Bits.value xs * 2^p : ℕ)) : ℤ)) : Dusk.day w) = _
    simp only [Int.cast_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hmod]
  apply Prod.ext
  · change Bits.sized (w+1) (Code.fill false (Code.tally p) ++ xs) = Dusk.trip _
    apply Bits.word_inject
    · rw [Dusk.trip_length, Bits.sized_length]
    · rw [Bits.sized_low, Bits.value_append, Code.fill_eq, Code.tally_length,
        Bits.zeroes, List.length_replicate, zero_add, Dusk.trips, hd, mul_comm]
      exact Nat.mod_eq_of_lt <| (scaled_digit_lt h).trans_le
        (Nat.pow_le_pow_right (by decide) (Nat.le_succ _))
  change Code.fill false (Code.tally (w+1)) = Dusk.trip _
  apply Bits.word_inject
  · simp [Code.fill_eq, w]
  · simp [Code.fill_eq, digitRecord, Grid.wrapMap]

@[simp]
theorem value_seed (k : ℕ) : value k (digitRecord k 1) = 1 := by
  simpa using value_digit (k := k) (n := 1) (Nat.one_le_pow _ _ (by decide))

end FixedPoint

end NearSquareRoot
end Computability
end OAI

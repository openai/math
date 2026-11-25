import OAI.Computability.BorderVNP.RoutingISACompactFrame

/-! # Individual bits of the packed cell descriptor

Even positions before the terminator contain one tags, and odd positions hold
the payload bits. At and beyond the terminator the stream is all zero. Reading
a bit by its word quotient and little-endian remainder gives this same stream.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CompactFrame

open VPVNP.BurstRAM

/-- The infinite zero extension of the terminated bit frame. -/
def letter (xs : List Bool) (j : ℕ) : Bool := (frameBits xs)[j]?.getD false

/-- The word containing bit address `j`, with zero beyond the packed array. -/
def atWord (w : ℕ) (xs : List Bool) (j : ℕ) : Word w := ((pack w xs)[j/w]?).getD 0

private theorem letter_cons (b : Bool) (xs : List Bool) (j : ℕ) :
    letter (b :: xs) (j+2) = letter xs j := rfl

/-- Each payload digit starts with a one tag. -/
theorem letter_tag (xs : List Bool) {i : ℕ} (hi : i < xs.length) : letter xs (2*i) = true := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons b xs ih =>
    cases i with
    | zero => rfl
    | succ i => rw [Nat.mul_succ, letter_cons, ih (by simpa using hi)]

/-- Immediately after its tag comes the original payload digit. -/
theorem letter_data (xs : List Bool) {i : ℕ} (hi : i < xs.length) : letter xs (2*i+1) = xs[i] := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons b xs ih =>
    cases i with
    | zero => rfl
    | succ i =>
      rw [show 2*(i+1)+1 = (2*i+1)+2 by omega, letter_cons]
      exact ih (by simpa using hi)

/-- The terminator and all remaining positions are zero. -/
theorem letter_end (xs : List Bool) {j : ℕ} (hj : 2*xs.length ≤ j) : letter xs j = false := by
  induction xs generalizing j with
  | nil => cases j <;> rfl
  | cons b xs ih =>
    simp only [List.length_cons, Nat.mul_succ] at hj
    obtain ⟨k, rfl⟩ : ∃ k, j = k+2 := ⟨j-2, by omega⟩
    exact (letter_cons b xs k).trans (ih (by omega))

private theorem input_bit {w : ℕ} (words : List (Word w)) (row col : ℕ) (hc : col < w) :
    (TeamPrivateCall.inputBits words)[row*w+col]?.getD false = (words[row]?.getD 0).val.testBit col := by
  induction words generalizing row with
  | nil => simp [TeamPrivateCall.inputBits]
  | cons x xs ih =>
    change ((List.ofFn (fun i : Fin w => x.val.testBit i.val)) ++ TeamPrivateCall.inputBits xs)[row*w+col]?.getD false = _
    cases row with
    | zero =>
      simp only [Nat.zero_mul, Nat.zero_add, List.getElem?_cons_zero, Option.getD_some]
      rw [List.getElem?_append_left (by simpa using hc)]
      simp [hc]
    | succ row =>
      rw [Nat.succ_mul, List.getElem?_append_right (by simp; omega), List.length_ofFn,
        show row*w+w+col-w = row*w+col by omega]
      exact ih row

private theorem padded_letter (xs : List Bool) (pad j : ℕ) :
    (frameBits xs ++ List.replicate pad false)[j]?.getD false = letter xs j := by
  by_cases h : j < (frameBits xs).length
  · exact congrArg (fun o => o.getD false) (List.getElem?_append_left h)
  · have hz : (frameBits xs)[j]? = none := List.getElem?_eq_none (by omega)
    rw [List.getElem?_append_right (by omega), letter, hz, List.getElem?_replicate]
    split <;> rfl

/-- Row and lane addressing reads the corresponding position of the original frame. -/
theorem packed_word_bit {w : ℕ} (hw : 0 < w) (xs : List Bool) (row col : ℕ) (hc : col < w) :
    (((pack w xs)[row]?).getD 0).val.testBit col = letter xs (row*w+col) := by
  rw [← input_bit _ row col hc, inputBits_pack hw, padded_letter]

/-- Quotient and remainder select the actual word and the little-endian lane. -/
theorem atWord_bit {w : ℕ} (hw : 0 < w) (xs : List Bool) (j : ℕ) :
    (atWord w xs j).val.testBit (j%w) = letter xs j := by
  rw [atWord, packed_word_bit hw xs (j/w) (j%w) (Nat.mod_lt j hw),
    Nat.mul_comm (j/w), Nat.div_add_mod]

/-- The packed interval includes the word holding the terminator, even at a word boundary. -/
theorem wordCount_terminator {w : ℕ} (hw : 0 < w) (xs : List Bool) :
    wordCount w xs = (2*xs.length)/w + 1 := by
  unfold wordCount
  rw [show 2*xs.length+1+w-1 = 2*xs.length+w by omega, Nat.add_div_right _ hw]

/-- Every data and tag position, as well as the terminator, has a word in the array. -/
theorem word_in_range {w : ℕ} (hw : 0 < w) (xs : List Bool) (j : ℕ) (hj : j ≤ 2*xs.length) :
    j/w < (pack w xs).length := by
  rw [length_pack, ← wordCount, wordCount_terminator hw]
  exact Nat.lt_succ_of_le (Nat.div_le_div_right hj)

/-- No high bits of the final word need writing. At a word boundary this says
the entire last word, containing the terminator and padding, is zero. -/
theorem last_partial {w : ℕ} (hw : 0 < w) (xs : List Bool) :
    (atWord w xs (2*xs.length)).val % 2^(2*xs.length%w) = (atWord w xs (2*xs.length)).val := by
  apply Nat.mod_eq_of_lt
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  by_cases lane : i < w
  · rw [atWord, packed_word_bit hw xs _ _ lane]
    apply letter_end
    have h := Nat.div_add_mod (2*xs.length) w
    rw [Nat.mul_comm] at h
    omega
  · apply Nat.testBit_lt_two_pow
    exact (atWord w xs (2*xs.length)).isLt.trans_le (Nat.pow_le_pow_right (by decide) (by omega))

end RoutingISA.CompactFrame

end BorderVNP
end Computability
end OAI

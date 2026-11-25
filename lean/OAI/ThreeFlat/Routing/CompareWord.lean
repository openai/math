import OAI.ThreeFlat.Routing.CompareBits
import OAI.ThreeFlat.Routing.SwitchPins
import OAI.Computability.QuantumFactoring.BitNumbers
import Mathlib.Data.Prod.Lex

namespace OAI
/-! # Numerical order on joined little-endian words

Appending the high word after the low word puts every nonzero high bit above
the entire low word. Thus the same strict comparator works for the lexicographic
order on two fields, including the original index used to break sorting ties.
-/

namespace ThreeFlat.Routing

private theorem prefixValue_sum (x : ℕ → Bool) (w : ℕ) :
    prefixValue x w = ∑ i : Fin w, 2 ^ i.val * (x i.val).toNat := by
  induction w with
  | zero => simp [prefixValue]
  | succ w ih =>
    rw [prefixValue, ih, Fin.sum_univ_castSucc]
    simp only [Fin.val_last, Fin.val_castSucc, Nat.mul_comm (x w).toNat]

/-- The comparator reads the ordinary positional value of its input. -/
theorem wordValue_sum {w : ℕ} (x : Fin w → Bool) :
    wordValue x = ∑ i : Fin w, 2 ^ i.val * (x i).toNat := by
  simp [wordValue, prefixValue_sum, wordDigits]

/-- The unsigned comparator and the tagged switch use the same address order. -/
theorem wordValue_addressEquiv {w : ℕ} (x : Fin w → Bool) :
    wordValue x = (addressEquiv w x).val := by
  change wordValue x = (ExactQuantumFactoring.bitsValue x).toNat
  rw [wordValue_sum, ExactQuantumFactoring.bitsValue_toNat]

theorem wordValue_lt_two_pow {w : ℕ} (x : Fin w → Bool) : wordValue x < 2 ^ w := by
  rw [wordValue_addressEquiv]
  exact (addressEquiv w x).isLt

/-- Appending the digits of the high part shifts its value by the low width. -/
theorem wordValue_append {w h : ℕ} (lo : Fin w → Bool) (hi : Fin h → Bool) :
    wordValue (Fin.append lo hi) = wordValue lo + 2 ^ w * wordValue hi := by
  rw [wordValue_sum, Fin.sum_univ_add, wordValue_sum, wordValue_sum, Finset.mul_sum]
  simp only [Fin.append_left, Fin.append_right, Fin.val_castAdd, Fin.val_natAdd,
    pow_add, Nat.mul_assoc]

/-- Comparing the concatenations compares high fields first, then low fields. -/
private theorem wordValue_append_lt_iff_nat {w h : ℕ} (lo lo' : Fin w → Bool) (hi hi' : Fin h → Bool) :
    wordValue (Fin.append lo hi) < wordValue (Fin.append lo' hi') ↔
      toLex (wordValue hi, wordValue lo) < toLex (wordValue hi', wordValue lo') := by
  rw [wordValue_append, wordValue_append, Prod.Lex.toLex_lt_toLex]
  have ordered (u v : Fin w → Bool) {a b : ℕ} (hab : a < b) :
      wordValue u + 2 ^ w * a < wordValue v + 2 ^ w * b := by
    calc
      _ < 2 ^ w * (a + 1) := by
        rw [Nat.mul_add, Nat.mul_one]
        have := wordValue_lt_two_pow u
        omega
      _ ≤ 2 ^ w * b := Nat.mul_le_mul_left _ hab
      _ ≤ _ := Nat.le_add_left _ _
  rcases lt_trichotomy (wordValue hi) (wordValue hi') with hh | hh | hh
  · exact iff_of_true (ordered lo lo' hh) (Or.inl hh)
  · simp [hh]
  · exact iff_of_false (not_lt.mpr (ordered lo' lo hh).le)
      (fun e => e.elim hh.not_gt (fun eqn => hh.ne eqn.1.symm))

/-- The high-key and low-index fields use the switch's finite address order. -/
theorem wordValue_append_lt_iff {m k : ℕ} (lo lo' : Fin m → Bool) (hi hi' : Fin k → Bool) :
    wordValue (Fin.append lo hi) < wordValue (Fin.append lo' hi') ↔
      toLex (addressEquiv k hi, addressEquiv m lo) <
        toLex (addressEquiv k hi', addressEquiv m lo') := by
  rw [wordValue_append_lt_iff_nat]
  simp only [Prod.Lex.toLex_lt_toLex, wordValue_addressEquiv, Fin.lt_def, Fin.val_inj]

end ThreeFlat.Routing

end OAI

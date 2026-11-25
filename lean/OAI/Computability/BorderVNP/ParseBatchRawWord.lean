import OAI.Computability.BorderVNP.ParseBatchRecordBits
import OAI.Computability.BorderVNP.ParseBatchWordArithmetic
import OAI.Computability.VPVNP.LiveHeaderBits

/-! # Converting raw parse-record fields to arithmetic words

The physical encoding puts the least significant bit first. The comparison and
arithmetic expressions read the most significant bit first, with zero extension
when a larger working width is needed.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseRecords

open VPVNP VerifierNetwork ParseBatchSort

/-- Reading the low `w` bits from most to least significant reconstructs the residue. -/
theorem bigValue_testBit (w a : ℕ) :
    value (fun i : Fin w => a.testBit (w-1-i.val)) = a % 2^w := by
  induction w with
  | zero => simp [value, Nat.mod_one]
  | succ w ih =>
    have ht (i : Fin w) : w-i.succ.val = w-1-i.val := by
      simp only [Fin.val_succ]
      omega
    have hb : (a.testBit w).toNat = a / 2^w % 2 := by
      rw [Nat.testBit_eq_decide_div_mod_eq]
      by_cases h : a / 2^w % 2 = 1 <;> simp [h]
      omega
    simp only [value, Fin.val_zero, Nat.sub_zero, Nat.add_sub_cancel, ht, ih, hb,
      pow_succ, Nat.mod_mul (a := 2^w) (b := 2)]
    ring

/-- A constant width-`w` word in most-significant-bit-first order. -/
def constWord {ι : Type*} (w a : ℕ) : Fin w → Expr ι :=
  fun i => .const (a.testBit (w-1-i.val))

/-- A constant word has its prescribed value when the width is sufficient. -/
theorem constWord_value {ι : Type*} (z : ι → Bool) (w a : ℕ) (ha : a < 2^w) :
    wordValue z (constWord w a) = a :=
  (bigValue_testBit w a).trans (Nat.mod_eq_of_lt ha)

/-- Each constant output bit uses a single constant formula node. -/
theorem constWord_size {ι : Type*} (w a : ℕ) (i : Fin w) :
    ((constWord w a i : Expr ι)).size = 1 := rfl

/-- Reverse the bit order of one raw word and zero-pad it to the working width. -/
def rawWord {v : ℕ} (w : ℕ) (f : Fin 6) (i : Fin w) : Expr (BitSlot v) :=
  if h : w-1-i.val < v then .input (.inr (f, ⟨w-1-i.val,h⟩)) else .const false

/-- Extending a raw physical word preserves its unsigned value exactly. -/
theorem rawWord_value {v w : ℕ} (hw : v ≤ w) (f : Fin 6) (z : BitSlot v → Bool) :
    wordValue z (rawWord w f) = (fieldsOfBits z).word f := by
  let a := (RAMSerialization.wordBits v).symm (fun j => z (.inr (f,j)))
  have he (i : Fin w) : (rawWord w f i).eval z = a.val.testBit (w-1-i.val) := by
    by_cases hi : w-1-i.val < v
    · simp only [rawWord, hi, dite_eq_left, BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit.Expr.eval]
      exact (congrFun ((RAMSerialization.wordBits v).apply_symm_apply (fun j => z (.inr (f,j))))
        ⟨w-1-i.val, hi⟩).symm.trans (LiveHeader.testBit_wordBits a _).symm
    · have hlt := a.isLt.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt hi))
      simp [rawWord, hi, BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit.Expr.eval,
        Nat.testBit_eq_false_of_lt hlt]
  simp only [wordValue, he, bigValue_testBit, word_fieldsOfBits]
  exact Nat.mod_eq_of_lt (a.isLt.trans_le (Nat.pow_le_pow_right (by decide) hw))

/-- Every bit of an extended field costs exactly one node. -/
theorem rawWord_size {v w : ℕ} (f : Fin 6) (i : Fin w) :
    ((rawWord w f i : Expr (BitSlot v))).size = 1 := by
  unfold rawWord
  split <;> rfl

end ParseRecords

end BorderVNP
end Computability
end OAI

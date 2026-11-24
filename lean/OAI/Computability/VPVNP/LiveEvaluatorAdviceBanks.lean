import OAI.Computability.VPVNP.LiveEvaluatorInitialize
import OAI.Computability.VPVNP.LiveHeaderAdvice

/-!
# Little-endian rows of the evaluator's distributed advice

A row may be shorter than a machine word. Only the requested source bits
enter it, and all higher bits and bits past the end of the source are zero.
Writing one verified source bit with the RAM's shift and bitwise-or opcodes
extends this partially assembled row. The same operation packs the raw
evaluator prefix and the separate table of permutation ordinals.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveEvaluatorAdviceBanks

open BurstRAM (Word Memory)
open BurstRAM.PrivateRAM (BinaryOp)
open RAMSerialization (wordBits arrayBits)
open PrimedInputRAM (encodeBit)

/-- Pack the requested low-order source bits of one advice row into a machine word, zeroing
unused positions and absent source bits. -/
def packedPrefix (w fw : ℕ) (raw : List Bool) (row count : ℕ) : Word w :=
  (wordBits w).symm (fun i => decide (i.val < fw ∧ i.val < count) && raw[row*fw+i.val]?.getD false)

/-- Pack a complete advice row at the specified field width, using zero padding past the end of
the raw advice. -/
def packedWord (w fw : ℕ) (raw : List Bool) (row : ℕ) := packedPrefix w fw raw row fw

theorem packedPrefix_bit (w fw : ℕ) (raw : List Bool) (row count : ℕ) (i : Fin w) :
    (packedPrefix w fw raw row count).val.testBit i.val =
      (decide (i.val < fw ∧ i.val < count) && raw[row*fw+i.val]?.getD false) := by
  rw [LiveHeader.testBit_wordBits]
  simp [packedPrefix]

private theorem extBits {w : ℕ} {a b : Word w} (h : ∀ i : Fin w, a.val.testBit i.val = b.val.testBit i.val) :
    a = b := by
  apply (wordBits w).injective
  funext i
  simpa only [LiveHeader.testBit_wordBits] using h i

theorem packedPrefix_zero (w fw : ℕ) (raw : List Bool) (row : ℕ) :
    packedPrefix w fw raw row 0 = 0 := by
  apply extBits
  intro i
  simp [packedPrefix_bit]

private theorem insertBit {w : ℕ} (v : Word w) (bit : Bool) (k : Fin w) (i : Fin w) :
    (BinaryOp.bitOr.eval v (BinaryOp.shiftLeft.eval (encodeBit w bit) (Fin.ofNat (2^w) k.val))).val.testBit i.val =
      (v.val.testBit i.val || (decide (k = i) && bit)) := by
  have hk : k.val < 2^w := k.isLt.trans (Nat.lt_two_pow_self (n := w))
  have hv : (1 : Word w).val = 1 := Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by have := k.isLt; omega))
  have hshift : BinaryOp.shiftLeft.eval (encodeBit w bit) (Fin.ofNat (2^w) k.val) =
      if bit then Fin.ofNat (2^w) (2^k.val) else 0 := by
    cases bit <;> simp only [BinaryOp.eval, encodeBit, Fin.val_ofNat, Nat.mod_eq_of_lt hk,
      k.isLt, ite_true, Bool.false_eq_true, ite_false, Fin.val_zero, hv, Nat.zero_shiftLeft, Nat.one_shiftLeft]
    rfl
  rw [hshift]
  cases bit <;> simp [BinaryOp.eval, Nat.testBit_mod_two_pow, i.isLt, Nat.testBit_or,
    Nat.testBit_two_pow, Fin.ext_iff]

/-- Inserting the next source bit is exactly one native shift followed by bitwise or. -/
theorem packedPrefix_succ (w fw : ℕ) (raw : List Bool) (row k : ℕ) (hk : k < fw) (hw : fw ≤ w) :
    BinaryOp.bitOr.eval (packedPrefix w fw raw row k)
      (BinaryOp.shiftLeft.eval (encodeBit w (raw[row*fw+k]?.getD false)) (Fin.ofNat (2^w) k)) =
      packedPrefix w fw raw row (k+1) := by
  apply extBits
  intro i
  rw [insertBit (k := (⟨k,hk.trans_le hw⟩ : Fin w)), packedPrefix_bit, packedPrefix_bit]
  by_cases he : i.val = k
  · simp [Fin.ext_iff, he, hk]
  · by_cases hi : i.val < k
    · simp [Fin.ext_iff, hi, hi.trans hk, show i.val < k+1 by omega, Ne.symm he]
    · simp [Fin.ext_iff, hi, show ¬ i.val < k+1 by omega, Ne.symm he]

/-- A cropped column past the end of the raw input leaves the row unchanged. -/
theorem packedPrefix_skip (w fw : ℕ) (raw : List Bool) (row k : ℕ)
    (hend : raw.length ≤ row*fw+k) :
    packedPrefix w fw raw row (k+1) = packedPrefix w fw raw row k := by
  apply extBits
  intro i
  rw [packedPrefix_bit, packedPrefix_bit]
  by_cases he : i.val = k
  · simp [he, List.getElem?_eq_none hend]
  · by_cases hi : i.val < k
    · simp [hi, show i.val < k+1 by omega]
    · simp [hi, show ¬ i.val < k+1 by omega]

/-- Full-width output rows are the words the midpoint initialization actually reads. -/
theorem packedWord_inputWord (w : ℕ) (raw : List Bool) (row : ℕ) :
    packedWord w w raw row = LiveEvaluatorInitialize.inputWord w raw row := by
  apply (wordBits w).injective
  funext i
  simp [packedWord, packedPrefix, LiveEvaluatorInitialize.inputWord]

/-- Packing a serialized array row returns that ordinal, extended to the runtime word width. -/
theorem packedWord_arrayBits {w t fw : ℕ} (hw : fw ≤ w) (values : Fin t → Word fw) (j : Fin t) :
    packedWord w fw (List.ofFn (arrayBits t fw values)) j.val =
      Fin.castLE (Nat.pow_le_pow_right (by decide : 0 < 2) hw) (values j) := by
  apply extBits
  intro i
  rw [packedWord, packedPrefix_bit]
  by_cases hi : i.val < fw
  · let k : Fin fw := ⟨i.val,hi⟩
    let ix := finProdFinEquiv (j,k)
    have hv : ix.val = j.val*fw+i.val := by simp [ix,k,finProdFinEquiv,Nat.add_comm,Nat.mul_comm]
    have hbits : arrayBits t fw values ix = wordBits fw (values j) k := by
      simp [ix,arrayBits]
    rw [← hv, List.getElem?_ofFn, dite_eq_left ix.isLt]
    simp [hi, hbits, ← LiveHeader.testBit_wordBits, k]
  · have hz : (values j).val.testBit i.val = false := Nat.testBit_lt_two_pow (by
      exact (values j).isLt.trans_le (Nat.pow_le_pow_right (by decide) (le_of_not_gt hi)))
    simpa [hi] using hz.symm

end LiveEvaluatorAdviceBanks

end VPVNP
end Computability
end OAI

import OAI.ThreeFlat.RAM.DescriptorExpr
import Mathlib.Data.ZMod.Defs

namespace OAI
/-! # Native generation of the unused slots of a fixed-capacity factor stream -/

namespace ThreeFlat.RAM.HistoryPadScan

open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM DescriptorExpr Fin.CommRing

variable {w k : ℕ}

/-- Inputs are a word offset in the padding suffix, its number of zero-test rows,
the first unused hidden bit's absolute address, and the zero-test table identifier. -/
def padTailWord : Term w k 4 :=
  .bind (.literal 4) <|
  .bind (.binary .div 1 0) <|           -- row
  .bind (.binary .mod 2 1) <|           -- column
  .bind (.literal 0) <|
  .bind (.literal 3) <|
  .bind (.literal 1) <|
  .bind (.binary .add 8 4) <|           -- hidden bit address
  .bind (.binary .add 10 1) <|          -- unit table ID
  .bind (.select .eq 5 4 1 4) <|       -- source of the zero-test row
  .bind (.select .eq 6 4 12 0) <|      -- zero-test record word
  .bind (.select .eq 7 5 2 6) <|       -- unit record word
  .bind (.select .lt 9 12 1 0) <|      -- select the record type
  .result 0

def padWord (off force first tag : Word w) : Word w :=
  let i := BinaryOp.eval .div off 4
  let j := BinaryOp.eval .mod off 4
  if i < force then
    if j = 3 then tag else if j = 0 then first+i else 0
  else if j = 3 then tag+1 else 0

set_option maxRecDepth 2048 in
theorem eval_padTailWord (data : Fin k → Word w) (m : Memory w) (v : Fin 4 → Word w) :
    padTailWord.eval data m v = padWord (v 0) (v 1) (v 2) (v 3) := by
  let i := BinaryOp.eval .div (v 0) 4
  let j := BinaryOp.eval .mod (v 0) 4
  change (if Comparison.lt.test i (v 1) then
    (if Comparison.eq.test j 3 then v 3 else if Comparison.eq.test j 0 then v 2+i else 0)
    else if Comparison.eq.test j 3 then v 3+1 else 0) = _
  simp [Comparison.test, padWord, i, j]

@[simp] theorem binds_padTailWord : (padTailWord (w := w) (k := k)).binds = 12 := rfl

/-- The actual word-sized row lookup for a bounded four-word record. -/
theorem padWord_at (i force : ℕ) (j : Fin 4) (first tag : Word w)
    (hw : 4 < 2^w) (hof : 4*i+j.val < 2^w) (hf : force < 2^w) :
    padWord ((4*i+j.val : ℕ) : Word w) (force : Word w) first tag =
      if i < force then (if j.val = 3 then tag else if j.val = 0 then first+(i : Word w) else 0)
      else if j.val = 3 then tag+1 else 0 := by
  have hj := j.isLt
  have four : (4 : Word w).val = 4 := show 4 % 2^w = 4 from Nat.mod_eq_of_lt hw
  have row : BinaryOp.eval .div ((4*i+j.val : ℕ) : Word w) 4 = (i : Word w) := by
    simp only [BinaryOp.eval, Fin.val_cast_of_lt hof, four, show (4*i+j.val)/4=i by omega]; rfl
  have col : BinaryOp.eval .mod ((4*i+j.val : ℕ) : Word w) 4 = (j.val : Word w) := by
    simp only [BinaryOp.eval, Fin.val_cast_of_lt hof, four, show (4*i+j.val)%4=j.val by omega]; rfl
  have ri : ((i : Word w) : ℕ) = i := Fin.val_cast_of_lt (by omega)
  have cj : ((j.val : Word w) : ℕ) = j.val := Fin.val_cast_of_lt (by omega)
  have v3 : (3 : Word w).val = 3 := show 3 % 2^w = 3 from Nat.mod_eq_of_lt (by omega)
  have lt : ((i : Word w) < (force : Word w)) ↔ i < force := by
    change ((i : Word w) : ℕ) < ((force : Word w) : ℕ) ↔ _
    rw [ri, Fin.val_cast_of_lt hf]
  have eq3 : ((j.val : Word w) = 3) ↔ j.val = 3 := by rw [Fin.ext_iff, cj, v3]
  have eq0 : ((j.val : Word w) = 0) ↔ j.val = 0 := by rw [Fin.ext_iff, cj]; rfl
  simp only [padWord, row, col, lt, eq3, eq0]

end ThreeFlat.RAM.HistoryPadScan

end OAI

import OAI.Computability.MultitapeWeakETH.Machine
import OAI.Computability.VPVNP.RAMTapeWordSimple
import Mathlib.Data.Fin.Rev

/-! # Low-end block arithmetic for the folded difference processors

The verified VPVNP word-RAM subtraction scan emits the modular difference
least significant bit first. Splitting that scan at arbitrary block boundaries
passes just one Boolean borrow. The final partial block needs no padding.
-/

namespace OAI.Computability.MultitapeWeakETH

open IntegerMultiplication VPVNP

/-- Reindex the VPVNP fixed-width encoding into the physical machine's
most-significant-first word convention. -/
def residueWord (n : ℕ) : Fin (2^n) ≃ Word n :=
  (RAMSerialization.wordBits n).trans (Fin.revPerm.arrowCongr (Equiv.refl Bool))

theorem residueWord_reverse {n : ℕ} (a : Fin (2^n)) :
    (List.ofFn (residueWord n a)).reverse = BurstRAM.wordBits a := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_reverse,List.length_ofFn,List.getElem_ofFn,BurstRAM.wordBits]
    apply congrArg (RAMSerialization.wordBits n a)
    apply Fin.ext
    simp only [Fin.revPerm_symm,Fin.revPerm_apply,Fin.val_rev]
    simp only [BurstRAM.length_wordBits] at hj
    omega

private theorem reverse_value (x : List Bool) : bitValue x.reverse = TapeWord.value x := by
  induction x with
  | nil => rfl
  | cons bit rest ih =>
    rw [List.reverse_cons]
    simp only [bitValue,List.foldl_append,List.foldl_cons,List.foldl_nil,TapeWord.value]
    unfold bitValue at ih
    omega

theorem residueWord_value {n : ℕ} (a : Fin (2^n)) : bitValue (List.ofFn (residueWord n a)) = a.val := by
  have h := reverse_value (List.ofFn (residueWord n a)).reverse
  rw [List.reverse_reverse,residueWord_reverse,TapeWord.value_wordBits] at h
  exact h

private theorem testBit_value (xs : List Bool) (i : ℕ) (h : i < xs.length) :
    (TapeWord.value xs).testBit i = xs[i] := by
  induction xs generalizing i with
  | nil => simp at h
  | cons x xs ih =>
    have hx : x.toNat < 2^1 := by cases x <;> decide
    rw [TapeWord.value,Nat.add_comm,← pow_one (2:ℕ),Nat.testBit_two_pow_mul_add _ hx]
    cases i with
    | zero => cases x <;> rfl
    | succ i => simpa using ih i (by simpa using h)

theorem residueWord_digit {n : ℕ} (a : Fin (2^n)) (i : Fin n) :
    residueWord n a i = a.val.testBit (n-1-i.val) := by
  let w := List.ofFn (residueWord n a)
  have h : n-1-i.val < w.reverse.length := by simp [w]; omega
  have digit := testBit_value _ _ h
  have val : TapeWord.value w.reverse = a.val := by
    rw [show w.reverse = BurstRAM.wordBits a from residueWord_reverse a,TapeWord.value_wordBits]
  rw [val,List.getElem_reverse] at digit
  apply Eq.trans _ digit.symm
  simp only [w,List.length_ofFn,List.getElem_ofFn]
  apply congrArg (residueWord n a)
  apply Fin.ext
  simp only
  omega

theorem lowProduct_residueWord {n : ℕ} (x y : Fin (2^n)) :
    lowProduct (residueWord n x) (residueWord n y) = residueWord n (x*y) := by
  funext i
  have h : n-1-i.val < n := by omega
  simp [lowProduct,residueWord_digit,residueWord_value,Fin.val_mul,Nat.testBit_mod_two_pow,h]

namespace Difference
open TapeWord

theorem scan_append (step : Bool → Bool → Bool → Bool × Bool) (c : Bool)
    (x y a b : List Bool) (len : x.length = y.length) :
    scan step c (x++a) (y++b) =
      let p := scan step c x y
      let q := scan step p.2 a b
      (p.1++q.1,q.2) := by
  induction x generalizing y c with
  | nil => cases y with
    | nil => rfl
    | cons d ds => simp at len
  | cons x xs ih =>
    cases y with
    | nil => simp at len
    | cons y ys =>
      simp only [List.cons_append,scan]
      rw [ih _ _ (Nat.succ.inj len)]

private theorem scan_take (step : Bool → Bool → Bool → Bool × Bool) (c : Bool)
    {x y : List Bool} (len : x.length = y.length) (k : ℕ) :
    (scan step c (x.take k) (y.take k)).1 = (scan step c x y).1.take k := by
  have same : (x.take k).length = (y.take k).length := by simp [len]
  have h := scan_append step c (x.take k) (y.take k) (x.drop k) (y.drop k) same
  simp only [List.take_append_drop] at h
  by_cases hk : k ≤ x.length
  · have length : (scan step c (x.take k) (y.take k)).1.length = k := by
      rw [length_scan _ _ _ _ same,List.length_take,min_eq_left hk]
    rw [h]
    exact (List.take_left' length).symm
  · simp [List.take_of_length_le (by omega : x.length ≤ k),List.take_of_length_le (by omega : y.length ≤ k),
      List.take_of_length_le (show (scan step c x y).1.length ≤ k by rw [length_scan _ _ _ _ len]; omega)]

def chunk (start size : ℕ) (xs : List Bool) := (xs.drop start).take size
def borrow (a b : List Bool) (k : ℕ) := (subScan false (a.take k) (b.take k)).2

/-- A processor sees the two input blocks and the lower-block borrow. It
computes both its own block of the global difference and the next borrow. -/
theorem subtract_chunk {x y : List Bool} (len : x.length = y.length) (start size : ℕ) :
    subScan (borrow x y start) (chunk start size x) (chunk start size y) =
      (chunk start size (subScan false x y).1,borrow x y (start+size)) := by
  have same : (x.take start).length = (y.take start).length := by simp [len]
  have h := scan_append subBit false (x.take start) (y.take start) (chunk start size x)
    (chunk start size y) same
  change subScan false _ _ = _ at h
  simp only [chunk,← List.take_add] at h
  apply Prod.ext
  · have whole := congrArg Prod.fst h
    change (subScan false (x.take (start+size)) (y.take (start+size))).1 =
      (subScan false (x.take start) (y.take start)).1 ++
      (subScan (borrow x y start) (chunk start size x) (chunk start size y)).1 at whole
    rw [scan_take subBit false len,scan_take subBit false len] at whole
    rw [List.take_add] at whole
    exact (List.append_cancel_left whole).symm
  · exact (congrArg Prod.snd h).symm

/-- The scan implements subtraction modulo 2ⁿ, including when it borrows
past the most significant bit. -/
theorem subtract_residues {n : ℕ} (x y : Fin (2^n)) (start size : ℕ) :
    let a := BurstRAM.wordBits x
    let b := BurstRAM.wordBits y
    subScan (borrow a b start) (chunk start size a) (chunk start size b) =
      (chunk start size (BurstRAM.wordBits (x-y)),borrow a b (start+size)) := by
  have full : (subScan false (BurstRAM.wordBits x) (BurstRAM.wordBits y)).1 = BurstRAM.wordBits (x-y) :=
    ScanOp.result_wordBits .sub x y
  simpa only [full] using subtract_chunk (x:=BurstRAM.wordBits x) (y:=BurstRAM.wordBits y) (by simp) start size

end Difference
end OAI.Computability.MultitapeWeakETH

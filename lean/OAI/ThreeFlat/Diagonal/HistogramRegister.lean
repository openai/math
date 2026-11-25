import OAI.ThreeFlat.Diagonal.MotifHistogram
import OAI.ThreeFlat.Diagonal.MotifBinaryPacking
import OAI.ThreeFlat.Diagonal.HistoryCode
import Mathlib.Data.Fin.Rev

namespace OAI
/-! # Canonical chronological records for all motif histograms of a stage -/

namespace ThreeFlat.Diagonal.HistogramRegister

open MotifOuterTerms HistoryContraction
open scoped BigOperators Classical
noncomputable section

variable {M K W : ℕ}

/-- Each row occupies exactly `K` words. The tile selected from its old widths fixes the
number of active symbols and the sum of their counts. -/
structure Rows (M K W : ℕ) where
  symbols : Fin M → ℕ
  copies : Fin M → ℕ
  fitSymbols : ∀ i, symbols i ≤ K
  fitCopies : ∀ i, copies i < 2^W

abbrev Choices (R : Rows M K W) := (i : Fin M) → Histogram (Fin (R.symbols i)) (R.copies i)
abbrev Words (M K W : ℕ) := Fin M → Fin K → Fin (2^W)

variable (R : Rows M K W)

def admitted (x : Words M K W) : Prop := ∀ i,
  (∑ s : Fin (R.symbols i), (x i (s.castLE (R.fitSymbols i))).val) = R.copies i ∧
    ∀ s : Fin K, R.symbols i ≤ s.val → x i s = 0

def words (h : Choices R) : Words M K W := fun i s =>
  if hs : s.val < R.symbols i then
    ⟨((h i).1 ⟨s.val,hs⟩).val, (Nat.le_of_lt_succ ((h i).1 ⟨s.val,hs⟩).isLt).trans_lt (R.fitCopies i)⟩
  else 0

@[simp] theorem words_active (h : Choices R) (i : Fin M) (s : Fin (R.symbols i)) :
    (words R h i (s.castLE (R.fitSymbols i))).val = ((h i).1 s).val := by simp [words,s.isLt]

theorem admit_words (h : Choices R) : admitted R (words R h) := by
  intro i
  refine ⟨?_,fun s hs => ?_⟩
  · simpa only [words_active] using (h i).2
  · simp [words,Nat.not_lt.mpr hs]

def choices (x : Words M K W) (hx : admitted R x) : Choices R := fun i =>
  ⟨fun s => ⟨(x i (s.castLE (R.fitSymbols i))).val, Nat.lt_succ_of_le (by
      rw [← (hx i).1]
      exact Finset.single_le_sum (fun j _ => Nat.zero_le (x i (j.castLE (R.fitSymbols i))).val) (Finset.mem_univ s))⟩,
    (hx i).1⟩

@[simp] theorem words_choices (x : Words M K W) (hx : admitted R x) :
    words R (choices R x hx) = x := by
  funext i s
  by_cases h : s.val < R.symbols i
  · apply Fin.ext
    simp [words,choices,h]
  · rw [show words R (choices R x hx) i s=0 by simp [words,h],(hx i).2 s (Nat.le_of_not_gt h)]

@[simp] theorem choices_words (h : Choices R) : choices R (words R h) (admit_words R h) = h := by
  funext i
  apply Subtype.ext
  funext s
  apply Fin.ext
  exact words_active R h i s

/-- The physical bit ordinal is `(row*K+symbol)*W+digit`. Digit zero is the most significant bit,
matching the five-instruction word scanner in `RAM.ReadPackedWord`. -/
def address (i : Fin M) (s : Fin K) (b : Fin W) : Fin (M*K*W) :=
  finProdFinEquiv (finProdFinEquiv (i,s),b)

theorem address_val (i : Fin M) (s : Fin K) (b : Fin W) :
    (address i s b).val = (i.val*K+s.val)*W+b.val := by
  change b.val + W*(s.val+K*i.val) = _
  ac_rfl

private def reverseWord (w : ℕ) : (Fin w → Bool) ≃ Fin (2^w) :=
  (Equiv.arrowCongr (@Fin.revPerm w) (Equiv.refl Bool)).trans (MotifBinaryPacking.word w)

def bitTable : Words M K W ≃ (Fin (M*K*W) → Bool) where
  toFun x a :=
    let ib := finProdFinEquiv.symm a
    let is := finProdFinEquiv.symm ib.1
    (reverseWord W).symm (x is.1 is.2) ib.2
  invFun v i s := reverseWord W (fun b => v (address i s b))
  left_inv x := by
    funext i s
    simp [address]
  right_inv v := by
    funext a
    obtain ⟨⟨u,b⟩,rfl⟩ := finProdFinEquiv.surjective a
    obtain ⟨⟨i,s⟩,rfl⟩ := finProdFinEquiv.surjective u
    simp [address]

@[simp] theorem bitTable_at (x : Words M K W) (i : Fin M) (s : Fin K) (b : Fin W) :
    bitTable x (address i s b) = (x i s).val.testBit (W-1-b.val) := by
  simp only [bitTable,address,Equiv.coe_fn_mk,Equiv.symm_apply_apply]
  change (x i s).val.testBit (W-(b.val+1)) = _
  congr 1; omega

private def listBits {n : ℕ} (v : List Bool) (len : v.length=n) (i : Fin n) :=
  v.get (i.cast len.symm)

@[simp] private theorem bits_ofFn {n : ℕ} (v : Fin n→Bool) :
    listBits (List.ofFn v) List.length_ofFn=v := by
  funext i
  simp [listBits]

@[simp] private theorem ofFn_listBits {n : ℕ} (v : List Bool) (len : v.length=n) :
    List.ofFn (listBits v len)=v := by
  subst n
  exact List.ofFn_get v

private def decodeWords {count : ℕ} (order : Fin count ≃ Choices R) (x : Words M K W) : Option (Fin count) :=
  if hx : admitted R x then some (order.symm (choices R x hx)) else none

private theorem decodeWords_write {count : ℕ} (order : Fin count ≃ Choices R) (i : Fin count) :
    decodeWords R order (words R (order i))=some i := by
  unfold decodeWords
  rw [dite_eq_left (admit_words R (order i)),choices_words,Equiv.symm_apply_apply]

/-- Fixed-size list parser for one stage. Insufficient input, a wrong histogram sum,
or a nonzero unused field fails; every successful parse reconstructs those exact bits. -/
def record {count : ℕ} (order : Fin count ≃ Choices R) : Record count where
  width := M*K*W
  write := fun j => List.ofFn (bitTable (words R (order j)))
  read := fun v => if hv : v.length=M*K*W then
    decodeWords R order (bitTable.symm (listBits v hv)) else none
  write_length _ := List.length_ofFn
  read_write i := by
    rw [dite_eq_left List.length_ofFn,bits_ofFn,Equiv.symm_apply_apply,decodeWords_write]
  write_read v i h := by
    by_cases hv : v.length=M*K*W
    · let x : Words M K W := bitTable.symm (listBits v hv)
      by_cases hx : admitted R x
      · have decision : order.symm (choices R x hx)=i := by
          apply Option.some.inj
          rw [dite_eq_left hv] at h
          change decodeWords R order x=some i at h
          rwa [decodeWords,dite_eq_left hx] at h
        rw [←decision,Equiv.apply_symm_apply,words_choices]
        change List.ofFn (bitTable (bitTable.symm (listBits v hv)))=v
        rw [Equiv.apply_symm_apply,ofFn_listBits]
      · have bad : ¬admitted R (bitTable.symm (listBits v hv)) := hx
        simp only [dite_eq_left hv,decodeWords,dite_eq_right bad,reduceCtorEq] at h
    · simp only [dite_eq_right hv,reduceCtorEq] at h

/-- Arbitrarily named physical motifs and tile letters can use their actual row and symbol order. -/
def reindex {I : Type} {A : I → Type} [∀ i, Fintype (A i)] (idx : Fin M ≃ I)
    (letter : (i : Fin M) → Fin (R.symbols i) ≃ A (idx i)) :
    (∀ i : I, Histogram (A i) (R.copies (idx.symm i))) ≃ Choices R := by
  let per (i : Fin M) : Histogram (A (idx i)) (R.copies i) ≃ Histogram (Fin (R.symbols i)) (R.copies i) := {
    toFun h := ⟨fun s => h.1 (letter i s), ((letter i).sum_comp (fun s => (h.1 s).val)).trans h.2⟩
    invFun h := ⟨fun s => h.1 ((letter i).symm s), ((letter i).symm.sum_comp (fun s => (h.1 s).val)).trans h.2⟩
    left_inv h := by apply Subtype.ext; funext s; simp
    right_inv h := by apply Subtype.ext; funext s; simp
  }
  apply (Equiv.piCongrLeft' (fun i : I => Histogram (A i) (R.copies (idx.symm i))) idx.symm).trans
  apply Equiv.piCongrRight
  intro i
  simpa only [Equiv.symm_symm, Equiv.symm_apply_apply] using per i

end
end ThreeFlat.Diagonal.HistogramRegister

end OAI

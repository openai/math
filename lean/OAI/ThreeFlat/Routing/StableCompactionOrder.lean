import OAI.LinearAlgebra.SpectralBooks.Batcher
import OAI.ThreeFlat.Routing.CompareWord
import OAI.ThreeFlat.Routing.StableCompactionRank
import Mathlib.Order.Interval.Finset.Fin

namespace OAI
/-! # Stable compaction by sorting tagged rows

The high bit moves the inactive rows behind the active rows. The original row
index precedes the payload in the comparison, preserving the order even when
payload bits differ. Masking the sorted payloads fills the unused tail with zeros.
-/

namespace ThreeFlat.Routing.StableCompaction

open scoped Classical
noncomputable section

/-- Little-endian record with payload, original row index, and inactivity flag. -/
def record {m : ℕ} (M X : Fin (2^m) → Bool) (i : Fin (2^m)) : Fin ((1+m)+1) → Bool :=
  Fin.append (Fin.append (fun _ : Fin 1 => X i) ((addressEquiv m).symm i))
    (fun _ : Fin 1 => !(M i))

/-- Read the payload only when the high inactivity flag is clear. -/
def masked {m : ℕ} (z : Fin ((1+m)+1) → Bool) : Bool :=
  !(z (Fin.last (1+m))) && z 0

theorem masked_record {m : ℕ} (M X : Fin (2^m) → Bool) (i : Fin (2^m)) :
    masked (record M X i) = (M i && X i) := by
  change (!record M X i (Fin.natAdd (1+m) (0 : Fin 1)) &&
    record M X i (((0 : Fin 1).castAdd m).castAdd 1)) = _
  simp [record]

private theorem single_value (b : Bool) : wordValue (fun _ : Fin 1 => b) = b.toNat := by
  simp [wordValue_sum]

theorem record_value {m : ℕ} (M X : Fin (2^m) → Bool) (i : Fin (2^m)) :
    wordValue (record M X i) = (X i).toNat + 2*i.val + (2*2^m)*(!(M i)).toNat := by
  rw [record, wordValue_append, wordValue_append, single_value, single_value, wordValue_addressEquiv]
  simp [pow_add]

private theorem sorted_perm {m : ℕ} (M X : Fin (2^m) → Bool)
    (e : Equiv.Perm (Fin (2^m))) (sorted : Monotone fun j => wordValue (record M X (e j))) :
    ∀ j, masked (record M X (e j)) = compact M X j := by
  let s := active M
  let t := active (M ∘ e)
  have hcard : t.card = s.card := by
    apply Finset.card_bij (fun j _ => e j)
    · intro i hi
      simpa [s,t,active] using hi
    · intro i _ j _ hij
      exact e.injective hij
    · intro i hi
      refine ⟨e.symm i, ?_, e.apply_symm_apply _⟩
      simpa [s,t,active] using hi
  have small (i : Fin (2^m)) : (X i).toNat ≤ 1 := by cases X i <;> decide
  have earlier {i j : Fin (2^m)} (hij : i ≤ j) (hj : M (e j) = true) : M (e i) = true := by
    have h := sorted hij
    by_contra! hf
    simp only [record_value,hf,hj,Bool.not_false,Bool.not_true,Bool.toNat_true,
      Bool.toNat_false,Nat.mul_one,Nat.mul_zero,Nat.add_zero] at h
    have := (e j).isLt
    have := small (e j)
    omega
  have active_iff (j : Fin (2^m)) : M (e j) = true ↔ j.val < s.card := by
    rw [← hcard]
    constructor
    · intro hj
      have sub : Finset.Iic j ⊆ t := fun i hi => by
        simpa [t,active] using earlier (Finset.mem_Iic.mp hi) hj
      have hc := Finset.card_le_card sub
      rw [Fin.card_Iic] at hc
      omega
    · intro hj
      by_contra! hf
      have sub : t ⊆ Finset.Iio j := by
        intro i hi
        apply Finset.mem_Iio.mpr
        apply lt_of_not_ge
        intro hj'
        have := earlier hj' (show M (e i) = true by simpa [t,active] using hi)
        simp_all
      have := Finset.card_le_card sub
      rw [Fin.card_Iio] at this
      omega
  have hn : s.card ≤ 2^m := by simpa using s.card_le_univ
  let f (j : Fin s.card) := e (j.castLE hn)
  have mem (j : Fin s.card) : f j ∈ s := by
    simpa [f,s,active] using (active_iff (j.castLE hn)).mpr j.isLt
  have strict : StrictMono f := by
    intro i j hij
    have lt' : i.castLE hn < j.castLE hn := hij
    have h := sorted lt'.le
    have ai := (active_iff (i.castLE hn)).mpr i.isLt
    have aj := (active_iff (j.castLE hn)).mpr j.isLt
    simp only [record_value,ai,aj,Bool.not_true,Bool.toNat_false,Nat.mul_zero,Nat.add_zero] at h
    have ne : e (i.castLE hn) ≠ e (j.castLE hn) := fun he => lt'.ne (e.injective he)
    change (e (i.castLE hn)).val < (e (j.castLE hn)).val
    have nv : (e (i.castLE hn)).val ≠ (e (j.castLE hn)).val := fun he => ne (Fin.ext he)
    have := small (e (j.castLE hn))
    omega
  have eqf := Finset.orderEmbOfFin_unique rfl mem strict
  intro j
  rw [masked_record]
  by_cases h : j.val < s.card
  · have he : e j = s.orderEmbOfFin rfl ⟨j.val,h⟩ := congrFun eqf ⟨j.val,h⟩
    rw [(active_iff j).mpr h, Bool.true_and, he]
    simp [compact, s, show j.val < (active M).card from h]
  · have hj : M (e j) = false := by simpa using mt (active_iff j).mp h
    simp [compact, show ¬j.val < (active M).card from h,hj]

/-- The decoded record at output row `j` of Batcher's ascending sorter.
This is the specialization of `BitonicSort.sorted` to the compaction records. -/
def sortedRecord {m : ℕ} (M X : Fin (2^m) → Bool) (j : Fin (2^m)) : Fin ((1+m)+1) → Bool :=
  let addr := addressEquiv ((1+m)+1)
  addr.symm ((LinearAlgebra.SpectralBooks.Batcher.sortNet m).eval (fun i => addr (record M X i)) j)

/-- Sorting the records and reading the masked payload compacts the selected bits stably. -/
theorem masked_sorted {m : ℕ} (M X : Fin (2^m) → Bool) (j : Fin (2^m)) :
    masked (sortedRecord M X j) = compact M X j := by
  let a := fun i => addressEquiv ((1+m)+1) (record M X i)
  obtain ⟨hm,e,he⟩ := LinearAlgebra.SpectralBooks.Batcher.sortNet_correct a
  rw [he] at hm
  have hmono : Monotone fun i => wordValue (record M X (e i)) := by
    intro i k hik
    simpa only [wordValue_addressEquiv] using (show (a (e i)).val ≤ (a (e k)).val from hm hik)
  change masked ((addressEquiv ((1+m)+1)).symm
    ((LinearAlgebra.SpectralBooks.Batcher.sortNet m).eval a j)) = _
  rw [he]
  simpa [a] using sorted_perm M X e hmono j

end
end ThreeFlat.Routing.StableCompaction

end OAI

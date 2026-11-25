import OAI.ThreeFlat.Diagonal.HistogramRegister
import OAI.ThreeFlat.RAM.AdmissionBank
import Mathlib.Algebra.BigOperators.Fin

namespace OAI
/-! # The native stage guard recognizes canonical histogram register rows -/

namespace ThreeFlat.Diagonal.HistogramRegister
open Computability.VPVNP.BurstRAM PrivateRAM RAM
open scoped Classical BigOperators

private theorem sum_prefix {K d : ℕ} (fit : d≤K) (f : Fin K → ℕ)
    (padding : ∀ j, d≤j.val → f j=0) :
    (∑ j, f j)=∑ j : Fin d, f (j.castLE fit) := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le fit
  exact Fin.sum_trunc f (fun j => padding _ (by change d ≤ d+j.val; omega))

theorem prefix_valid_iff {K d : ℕ} (fit : d≤K) (counts : Fin K → ℕ) (copies : ℕ) :
    AdmissionPrefix.Valid K d counts copies ↔
      (∑ s : Fin d, counts (s.castLE fit))=copies ∧ ∀ s, d≤ s.val → counts s=0 := by
  rw [AdmissionPrefix.valid_iff_sum]
  constructor
  · rintro ⟨_,sum,pad⟩
    exact ⟨(sum_prefix fit counts pad).symm.trans sum,pad⟩
  · rintro ⟨sum,pad⟩
    exact ⟨fit,(sum_prefix fit counts pad).trans sum,pad⟩

/-- Read-only header, descriptor and dense-count layout for an untrusted packed register bank. -/
structure BankLayout {M K W : ℕ} (ctrl : ℕ) (rows : Rows M K W) (x : Words M K W) (mem : Memory W) : Prop where
  count : AdmissionBank.rowCount ctrl mem=M
  symbols (i : Fin M) : (mem (AdmissionBank.descBase ctrl mem + 3*i.val+2)).val = rows.symbols i
  copies (i : Fin M) : (mem (AdmissionBank.descBase ctrl mem + 3*i.val)).val = rows.copies i
  words (i : Fin M) (s : Fin K) : mem (AdmissionBank.denseBase ctrl mem + K*i.val+s.val) = x i s

theorem valid_rows_iff_admitted {M K W : ℕ} {ctrl : ℕ} {rows : Rows M K W}
    {x : Words M K W} {mem : Memory W} (h : BankLayout ctrl rows x mem) :
    (∀ i, i<AdmissionBank.rowCount ctrl mem → AdmissionBank.ValidRow ctrl K i mem) ↔ admitted rows x := by
  have row (i : Fin M) : AdmissionBank.ValidRow ctrl K i.val mem ↔
      (∑ s : Fin (rows.symbols i), (x i (s.castLE (rows.fitSymbols i))).val)=rows.copies i ∧
      ∀ s : Fin K, rows.symbols i≤ s.val → x i s=0 := by
    unfold AdmissionBank.ValidRow
    simp only [h.symbols,h.copies,h.words,prefix_valid_iff (rows.fitSymbols i),Fin.val_eq_zero_iff]
  rw [h.count]
  constructor
  · intro all i
    exact (row i).mp (all i.val i.isLt)
  · intro all i hi
    exact (row ⟨i,hi⟩).mpr (all ⟨i,hi⟩)

end ThreeFlat.Diagonal.HistogramRegister

end OAI

import OAI.Hierarchy.TaggedData
import OAI.ThreeFlat.Routing.PackedRows
import OAI.ThreeFlat.Routing.CompareWord
import Mathlib.Data.Fin.Tuple.Sort

namespace OAI
/-! # Flagged digit keys and the real prefix of a stable sort -/

namespace Hierarchy.Tagged.Radix.PassShape

/-- The dummy bit is the most significant partition key, so every real record
precedes all dummy records in the local and global sorts. -/
def maskedDigit {k w : ℕ} (digit : Fin k → Fin w) (isDummy : Fin w) : Fin (k+1) → Fin w :=
  Fin.snoc digit isDummy

end Hierarchy.Tagged.Radix.PassShape

namespace Hierarchy.Tagged.SortedBlock
open ThreeFlat Routing SortNetwork
open Radix.PassShape
open scoped Classical
noncomputable section

variable {l d w : ℕ}

def readKey (digit : Fin d → Fin w) (x : Fin w → Bool) : ℕ := (addressEquiv d (x ∘ digit)).val

def stable (digit : Fin d → Fin w) (x : Records l w) :=
  x ∘ Tuple.sort (fun i => addressEquiv d (x i ∘ digit))

def prefixSize (real : Fin w) (x : Records l w) : ℕ :=
  (Finset.univ.filter (fun i => x i real = true)).card

theorem prefixSize_le (real : Fin w) (x : Records l w) : prefixSize real x ≤ 2^l := by
  simpa [prefixSize] using Finset.card_filter_le Finset.univ (fun i => x i real = true)

/-- The moving sort flag occupies the high bit over the chosen digit. -/
theorem masked_value (digit : Fin d → Fin w) (dummy : Fin w) (v : Fin w → Bool) :
    readKey (maskedDigit digit dummy) v = readKey digit v + 2^d * (v dummy).toNat := by
  have eq : v ∘ maskedDigit digit dummy = Fin.append (v ∘ digit) (fun _ : Fin 1 => v dummy) := by
    rw [maskedDigit, Fin.comp_snoc, Fin.append_right_eq_snoc]
  simp only [readKey,←wordValue_addressEquiv,eq,wordValue_append]
  simp [wordValue_sum]

theorem sort_prefix (digit : Fin d → Fin w) (real dummy : Fin w) (input : Records l w)
    (flags : ∀ i, input i dummy = !(input i real)) :
    let out := stable (maskedDigit digit dummy) input
    ∀ i : Row l, out i real = true ↔ i.val < prefixSize real out := by
  let key := fun i : Row l => addressEquiv (d+1) (input i ∘ maskedDigit digit dummy)
  let e := Tuple.sort key
  let out := input ∘ e
  have mono : Monotone (fun i => (key (e i)).val) := fun i j h => Tuple.monotone_sort key h
  have test (i : Row l) : (key (e i)).val < 2^d ↔ out i real = true := by
    change readKey (maskedDigit digit dummy) (input (e i)) < _ ↔ _
    rw [masked_value, flags]
    have low := (addressEquiv d (input (e i) ∘ digit)).isLt
    change readKey digit (input (e i)) < 2^d at low
    change _ ↔ input (e i) real = true
    cases bit : input (e i) real <;> simp; omega
  change ∀ i : Row l, out i real = true ↔ i.val < prefixSize real out
  intro i
  have chosen := Tuple.lt_card_lt_iff_apply_lt_of_monotone (j := i) (a := 2^d) mono
  simpa only [test, prefixSize] using chosen.symm

/-- Sorting cannot increase the number of real lanes in a physical block
whose real input records were confined to its logical prefix. -/
theorem bound {b : ℕ} (digit : Fin d → Fin w) (real : Fin w) (input : Records l w)
    (supported : ∀ i, input i real = true → i.val < b) :
    prefixSize real (stable digit input) ≤ b := by
  let e := Tuple.sort (fun i => addressEquiv d (input i ∘ digit))
  let slots := Finset.univ.filter (fun i => (stable digit input) i real = true)
  let emb (x : slots) : Fin b := ⟨(e x.val).val,supported _ (Finset.mem_filter.mp x.property).2⟩
  have inj : Function.Injective emb := by
    intro x y eq
    apply Subtype.ext
    apply e.injective
    exact Fin.ext (congrArg (fun z : Fin b => z.val) eq)
  simpa only [Fintype.card_coe,Fintype.card_fin,slots,prefixSize] using
    Fintype.card_le_of_injective emb inj

end
end Hierarchy.Tagged.SortedBlock

end OAI

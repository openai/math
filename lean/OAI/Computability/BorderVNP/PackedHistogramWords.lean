import OAI.Computability.BorderVNP.ParseBatchLookupFrame
import OAI.Computability.BorderVNP.ParseBatchVerifierCountWords

/-! # Packing a bucket-sort record and its stable return address -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistogram

open ParseBatchLookup ParseBatchSort

variable {α β : Type*} {k b w : ℕ}

/-- The high and low bit fields commute with evaluating or renaming every bit. -/
theorem prepend_map (f : α → β) (a : Fin k → α) (v : Fin w → α) :
    f ∘ prepend a v = prepend (f ∘ a) (f ∘ v) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    simpa [prepend, Function.comp_def] using congrFun (ih (fun i => a i.succ)) j

/-- Selecting a high-field bit in a packed word returns the chosen input bit. -/
@[simp] theorem prepend_high (a : Fin k → α) (v : Fin w → α) (j : Fin k) :
    prepend a v (highPin w j) = a j := by
  induction k with
  | zero => exact j.elim0
  | succ k ih =>
    refine Fin.cases rfl (fun l => ?_) j
    simpa [prepend, highPin] using ih (fun i => a i.succ) l

/-- Selecting a low-field bit in a packed word returns the chosen input bit. -/
@[simp] theorem prepend_low (a : Fin k → α) (v : Fin w → α) (j : Fin w) :
    prepend a v (lowPin k j) = v j := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [prepend, lowPin] using ih (fun i => a i.succ)

/-- Sort key, query tag, original ordinal, and unsigned weight. -/
def record (address : Fin k → α) (query : α) (ordinal : Fin b → α) (weight : Fin w → α) :
    Fin (((w+b)+1)+k) → α := bits address query (prepend ordinal weight)

/-- Pin occupied by an address bit in a record. -/
def addressPin (b w : ℕ) (i : Fin k) : Fin (((w+b)+1)+k) := highPin ((w+b)+1) i

/-- Pin occupied by an ordinal bit in a record. -/
def ordinalPin (k w : ℕ) (i : Fin b) : Fin (((w+b)+1)+k) := lowPin k (highPin w i).succ

/-- Pin occupied by a weight bit in a record. -/
def weightPin (k b : ℕ) (i : Fin w) : Fin (((w+b)+1)+k) := lowPin k (lowPin b i).succ

@[simp] theorem record_address (a : Fin k → α) (q : α) (o : Fin b → α) (v : Fin w → α) (i : Fin k) :
    record a q o v (addressPin b w i) = a i := by simp [record, bits, addressPin]

@[simp] theorem record_ordinal (a : Fin k → α) (q : α) (o : Fin b → α) (v : Fin w → α) (i : Fin b) :
    record a q o v (ordinalPin k w i) = o i := by simp [record, bits, ordinalPin]

@[simp] theorem record_weight (a : Fin k → α) (q : α) (o : Fin b → α) (v : Fin w → α) (i : Fin w) :
    record a q o v (weightPin k b i) = v i := by simp [record, bits, weightPin]

/-- Evaluating a physical record evaluates each field separately. -/
theorem record_map (f : α → β) (a : Fin k → α) (q : α) (o : Fin b → α) (v : Fin w → α) :
    f ∘ record a q o v = record (f ∘ a) (f q) (f ∘ o) (f ∘ v) := by
  simp only [record, bits, prepend_map, Fin.comp_cons]

/-- Every pin belongs to one of the original fields, including the tag. -/
theorem record_const (x : α) :
    record (fun _ : Fin k => x) x (fun _ : Fin b => x) (fun _ : Fin w => x) = fun _ => x :=
  (record_map (fun _ : Unit => x) (fun _ => ()) () (fun _ => ()) (fun _ => ())).symm

/-- The high field of a return record is its original ordinal. -/
theorem ordinal_of_return (o : Fin b → Bool) (v : Fin w → Bool) :
    value (prepend o v) / 2^w = value o := by
  rw [value_prepend, Nat.mul_comm (value o), Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt (value_lt _), Nat.add_zero]

end PackedHistogram

end BorderVNP
end Computability
end OAI

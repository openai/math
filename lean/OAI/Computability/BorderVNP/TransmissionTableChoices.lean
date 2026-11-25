import OAI.Computability.BorderVNP.TransmissionProgram

/-! # Chronological guesses in a public transmission directory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Transmission

open VPVNP.BurstRAM

variable {w : ℕ}

/-- A local shared wire contributes one free bit per slot. A remote wire or a
data-delivery interval contributes no guesses. -/
def Range.choiceBits (row : Range w) (self : Word w) (bits : ℕ → Bool) : List Bool :=
  if row.selected self = some (some .sharedHere) then List.ofFn (fun j : Fin row.width.val => bits j.val) else []

/-- Chronological list of the free shared-wire guesses in a directory prefix. -/
def tableChoiceBits (rows : ℕ → Range w) (self : Word w) (bits : ℕ → ℕ → Bool) : ℕ → List Bool
  | 0 => []
  | i+1 => tableChoiceBits rows self bits i ++ (rows i).choiceBits self (bits i)

/-- Future row assignments do not change a completed memory prefix. -/
theorem tableMemory_congr (rows : ℕ → Range w) (self : Word w) (pub : Arg → Word w)
    (m : Memory w) {a b : ℕ → ℕ → Bool} {i : ℕ} (h : ∀ j < i, a j = b j) :
    tableMemory rows self pub m a i = tableMemory rows self pub m b i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [tableMemory, tableMemory, h i (by omega), ih (fun j hj => h j (by omega))]

/-- Future row assignments do not change a completed choice prefix. -/
theorem tableChoiceBits_congr (rows : ℕ → Range w) (self : Word w) {a b : ℕ → ℕ → Bool}
    {i : ℕ} (h : ∀ j < i, a j = b j) :
    tableChoiceBits rows self a i = tableChoiceBits rows self b i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [tableChoiceBits, tableChoiceBits, h i (by omega), ih (fun j hj => h j (by omega))]

/-- The size of the private choice stream is the sum of precisely the locally shared widths. -/
theorem tableChoiceBits_length (rows : ℕ → Range w) (self : Word w) (bits : ℕ → ℕ → Bool) (k : ℕ) :
    (tableChoiceBits rows self bits k).length = ∑ i ∈ Finset.range k,
      if (rows i).selected self = some (some .sharedHere) then (rows i).width.val else 0 := by
  induction k with
  | zero => simp [tableChoiceBits]
  | succ k ih =>
    by_cases h : (rows k).selected self = some (some .sharedHere) <;>
      simp [tableChoiceBits, ih, Finset.sum_range_succ, Range.choiceBits, h]

end RoutingISA.Transmission

end BorderVNP
end Computability
end OAI

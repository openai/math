import OAI.Computability.BorderVNP.CellBooleanBytecode
import Mathlib.Algebra.BigOperators.Fin

/-! # Guessing and discharging finite private flag blocks

Guesses push bits in temporal order. Enumerating the resulting stacks instead
of the temporal words is a bijection. After checking a block the deterministic
discard code removes its slots without changing the sign or guard.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellMacro

/-- A block of actual binary guess instructions sums once over every physical
top-of-stack vector, in the order in which offsets subsequently address it. -/
theorem value_guessBlock (n : ℕ) (ops : List Op) (f : Flags) (bank : List Bool) :
    value (List.replicate n .guess ++ ops) f bank =
      ∑ x : Fin n → Bool, value ops f (List.ofFn x ++ bank) := by
  induction n generalizing ops with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ', List.append_assoc, ih,
      ← (Fin.consEquiv (fun _ : Fin (n+1) => Bool)).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool]
    simp [value, Fin.consEquiv, Finset.sum_add_distrib, add_comm]

/-- Failed acceptance remains zero through arbitrary guesses and later tests. -/
theorem value_failed (ops : List Op) (minus : Bool) (v : List Bool) :
    value ops ⟨false, minus⟩ v = 0 := by
  induction ops generalizing minus v with
  | nil => rfl
  | cons op ops ih =>
    cases op <;> simp [value, Op.effect, ih]

/-- One three-instruction fragment discards a top slot by replacing it with
the constant truth value and consuming that truth value as a successful guard. -/
def discardBlock (n : ℕ) : List Op :=
  (List.replicate n [.literal false, .nand, .guard]).flatten

/-- Discarding a block restores the untouched data and preserves both flags. -/
theorem value_discardBlock (pushed bank : List Bool) (ops : List Op) (f : Flags) :
    value (discardBlock pushed.length ++ ops) f (pushed ++ bank) = value ops f bank := by
  induction pushed with
  | nil => rfl
  | cons b xs ih =>
    change value (([.literal false, .nand, .guard] ++ discardBlock xs.length) ++ ops) f
      (b :: xs ++ bank) = _
    rw [List.append_assoc]
    cases b <;> cases f with | mk ok minus => cases ok <;> exact ih

end CellMacro

namespace CellSparse

/-- Stack lookup agrees with a finite vector at every address in the freshly
guessed prefix. The remaining stack may have arbitrary contents. -/
theorem lookup_prefix {n : ℕ} (x : Fin n → Bool) (tail : List Bool) (i : Fin n) :
    lookup (List.ofFn x ++ tail) i.val = x i := by
  simp [lookup, List.head?_drop, List.getElem?_append_left, i.isLt]

/-- An offset past the guessed prefix reads the untouched continuation bank,
including the zero extension past its end. -/
theorem lookup_after_prefix {n : ℕ} (x : Fin n → Bool) (tail : List Bool) (i : ℕ) :
    lookup (List.ofFn x ++ tail) (n + i) = lookup tail i := by
  simp [lookup, List.drop_append, List.drop_eq_nil_of_le]

end CellSparse

end BorderVNP
end Computability
end OAI

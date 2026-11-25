import OAI.Computability.NearSquareRoot.KernelSelector
import OAI.Computability.NearSquareRoot.KernelSelectorAlign
import Mathlib.Tactic.FinCases

/-! # Looking up binary-kernel coefficients from a packed slot-major address -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelSelector

open IntegerMultiplication.Code
open KernelSelectorAlign

private theorem parity_eq_cast (n : ℕ) :
    (((decide (n % 2 = 1)).toNat : ℕ) : ZMod 2) = (n : ZMod 2) := by
  apply ZMod.val_injective
  rw [ZMod.val_natCast, ZMod.val_natCast]
  by_cases h : n % 2 = 1
  · simp [h]
  · have e : n % 2 = 0 := by omega
    simp [e]

private theorem count_ones_eq_sum {α : Type*} (s : List α) (φ : α → ZMod 2) :
    ((s.countP (fun x => decide (φ x = 1)) : ℕ) : ZMod 2) = (s.map φ).sum := by
  induction s with
  | nil => simp
  | cons x s ih =>
    have cases₂ (u : ZMod 2) : u = 0 ∨ u = 1 := by
      fin_cases u <;> first | exact Or.inl rfl | exact Or.inr rfl
    rcases cases₂ (φ x) with e | e <;> simp [e, ih, add_comm]

/-- The sum of the column signatures, in the fixed ordering of address slots. -/
def signature {a m d : ℕ} (slot : (Fin (m+1) ⊕ Fin d) × Bool ≃ Fin (a+1))
    (xs : List (Column a)) (j : Fin (m+1)) : ZMod 2 :=
  (xs.map fun c => queryColumn (fun i => get a c (slot i)) j).sum

/-- The finite map can return any encoded coefficient. The physical subroutine
selects it using all the exact quadratic phases over ℤ/2 on a slot-major address.
The returned data also include the original address and the scratch stacks are
restored on exit. The program is fixed before the number of columns is chosen. -/
theorem queryLookup {a m d : ℕ} {Y : Type} [Codec Y]
    (slot : (Fin (m+1) ⊕ Fin d) × Bool ≃ Fin (a+1))
    (table : (Fin (m+1) → ZMod 2) → Y) :
    Task List.length (slots a)
      (fun xs => .fork (send (table (signature slot xs))) (slots a xs)) := by
  let φ (j : Fin (m+1)) (c : Column a) := queryColumn (fun i => get a c (slot i)) j
  have scan := selectByParity a m (fun j c => decide (φ j c = 1))
    (fun p => table (fun j => (p j).toNat))
  have index (xs : List (Column a)) :
      (fun j : Fin (m+1) => (((decide (xs.countP (fun c => decide (φ j c = 1)) % 2 = 1)).toNat : ℕ) : ZMod 2)) =
        signature slot xs := by
    funext j
    rw [parity_eq_cast, count_ones_eq_sum]
    rfl
  simpa only [index] using scan

/-- The lookup task on the concrete P192 tapes. -/
theorem physicalQueryLookup {a m d : ℕ} {Y : Type} [Codec Y]
    (slot : (Fin (m+1) ⊕ Fin d) × Bool ≃ Fin (a+1))
    (table : (Fin (m+1) → ZMod 2) → Y) :
    ShortWord.PhysicalTask List.length (slots a)
      (fun xs => .fork (send (table (signature slot xs))) (slots a xs)) :=
  ShortWord.physicalTask (queryLookup slot table)

/-- A flat unmarked slot-major bit string suffices to select just the
coefficient. Its temporary address tree is discarded within the step bound. -/
theorem flatLookup {a m d : ℕ} {Y : Type} [Codec Y]
    (slot : (Fin (m+1) ⊕ Fin d) × Bool ≃ Fin (a+1))
    (table : (Fin (m+1) → ZMod 2) → Y) :
    Task List.length (fun xs => send (flatBits a xs))
      (fun xs => send (table (signature slot xs))) := by
  have look := queryLookup slot table
  obtain ⟨c,hc⟩ := look.sizeBound
  have trim := Task.dropRight (fun xs => send (table (signature slot xs))) (slots a)
  apply (((flatToSlots a).compose look).compose trim).bound (2*a+5+c)
  intro xs
  have e := hc xs
  have h := slots_count a xs
  change (send (table (signature slot xs))).count + (slots a xs).count + 1 ≤ _ at e
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one] at e h ⊢
  omega

end KernelSelector

end NearSquareRoot
end Computability
end OAI

import Mathlib.Logic.Equiv.Basic
import Mathlib.Order.Basic

/-! # XOR of rows selected by partial position maps

A pair of inverse read tables describes a matching between two chunks. Three
directed XORs exchange all matched positions at once. Applying three such
exchanges to the smaller endpoints, their partners, and the smaller endpoints
again implements an involution inside one chunk and restores the borrowed row.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled

variable {B : Type*}

/-- XOR each selected destination bit with its designated source bit. -/
def xorFrom (read : B → Option B) (src dst : B → Bool) (i : B) : Bool :=
  match read i with
  | none => dst i
  | some j => xor (dst i) (src j)

/-- Perform the three XORs of an exchange, targeting the second, first and second rows. -/
def exchangeRows (firstRead secondRead : B → Option B)
    (w : (B → Bool) × (B → Bool)) : (B → Bool) × (B → Bool) :=
  let second := xorFrom secondRead w.1 w.2
  let first := xorFrom firstRead second w.1
  (first, xorFrom secondRead first second)

/-- Replacing each selected bit by its source bit describes the net effect of the exchange. -/
def copyFrom (read : B → Option B) (src dst : B → Bool) (i : B) : Bool :=
  match read i with
  | none => dst i
  | some j => src j

theorem exchangeRows_eq (firstRead secondRead : B → Option B)
    (inverse : ∀ i j, firstRead i = some j ↔ secondRead j = some i)
    (w : (B → Bool) × (B → Bool)) :
    exchangeRows firstRead secondRead w =
      (copyFrom firstRead w.2 w.1, copyFrom secondRead w.1 w.2) := by
  apply Prod.ext
  · funext i
    cases e : firstRead i with
    | none => simp [exchangeRows, xorFrom, copyFrom, e]
    | some j =>
      have h := (inverse i j).mp e
      cases e1 : w.1 i <;> cases e2 : w.2 j <;> simp [exchangeRows, xorFrom, copyFrom, e, h, e1, e2]
  · funext j
    cases h : secondRead j with
    | none => simp [exchangeRows, xorFrom, copyFrom, h]
    | some i =>
      have e := (inverse i j).mpr h
      cases e1 : w.1 i <;> cases e2 : w.2 j <;> simp [exchangeRows, xorFrom, copyFrom, e, h, e1, e2]

variable [LinearOrder B]

/-- Borrow the position with the same index for each smaller endpoint. -/
def borrowIdRead (q : Equiv.Perm B) (i : B) : Option B := if i < q i then some i else none

/-- A borrowed smaller endpoint reads its larger partner in the original row. -/
def borrowUpRead (q : Equiv.Perm B) (i : B) : Option B := if i < q i then some (q i) else none

/-- A larger endpoint reads its partner at the borrowed position. -/
def borrowDownRead (q : Equiv.Perm B) (i : B) : Option B := if q i < i then some (q i) else none

private theorem borrowId_inverse (q : Equiv.Perm B) (i j : B) :
    borrowIdRead q i = some j ↔ borrowIdRead q j = some i := by
  by_cases e : i = j
  · subst j; rfl
  · simp [borrowIdRead, e, Ne.symm e]

private theorem borrowPartner_inverse (q : Equiv.Perm B) (hq : Function.Involutive q) (i j : B) :
    borrowDownRead q i = some j ↔ borrowUpRead q j = some i := by
  by_cases e : q i = j
  · subst j
    simp [borrowDownRead, borrowUpRead, hq i]
  · have f : q j ≠ i := fun h => e ((hq j).symm ▸ congrArg q h.symm)
    simp [borrowDownRead, borrowUpRead, e, f]

/-- Nine directed XORs implement the local position involution on the first
row. All second-row data are restored, regardless of their initial values. -/
theorem borrowRows_correct (q : Equiv.Perm B) (hq : Function.Involutive q) (C D : B → Bool) :
    exchangeRows (borrowIdRead q) (borrowIdRead q)
      (exchangeRows (borrowDownRead q) (borrowUpRead q)
        (exchangeRows (borrowIdRead q) (borrowIdRead q) (C,D))) = (C ∘ q,D) := by
  simp only [exchangeRows_eq _ _ (borrowId_inverse q), exchangeRows_eq _ _ (borrowPartner_inverse q hq)]
  apply Prod.ext <;> funext i
  all_goals
    by_cases lt : i < q i
    · have ge := lt.not_gt
      simp only [copyFrom, borrowUpRead, borrowDownRead, borrowIdRead, hq i, lt, ge, ite_true,
        ite_false, Function.comp_apply]
    · by_cases gt : q i < i
      · simp only [copyFrom, borrowUpRead, borrowDownRead, borrowIdRead, hq i, lt, gt, ite_true,
          ite_false, Function.comp_apply]
      · have eq : q i = i := le_antisymm (le_of_not_gt lt) (le_of_not_gt gt)
        simp [copyFrom, borrowUpRead, borrowDownRead, borrowIdRead, eq]

end Controlled

end NearSquareRoot
end Computability
end OAI

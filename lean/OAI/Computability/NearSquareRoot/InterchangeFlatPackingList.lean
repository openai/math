import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Logic.Function.Basic

/-!
# Packing a sparse index set into a dense list

Each unused slot holds the same default used for out-of-bounds reads. A finite
enumeration of the occupied indices suffices to compute the packed list.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FlatAtlas.PackingList

variable {α β : Type*}

/-- The dense representation of an indexed family, padded with `d` at holes. -/
noncomputable def pack (d : β) (idx : α → ℕ) (N : ℕ) (w : α → β) : List β :=
  List.ofFn fun i : Fin N => Function.extend idx w (fun _ => d) i.val

@[simp] theorem length_pack (d : β) (idx : α → ℕ) (N : ℕ) (w : α → β) :
    (pack d idx N w).length = N := List.length_ofFn

theorem getD_pack (d : β) (idx : α → ℕ) (N : ℕ) (w : α → β)
    (hinj : Function.Injective idx) (x : α) (hx : idx x < N) :
    (pack d idx N w).getD (idx x) d = w x := by
  rw [List.getD_eq_getElem _ _ (by simpa using hx)]
  simp [pack, hinj.extend_apply]

theorem getD_pack_unused (d : β) (idx : α → ℕ) (N : ℕ) (w : α → β)
    (i : ℕ) (hi : ∀ x, idx x ≠ i) : (pack d idx N w).getD i d = d := by
  by_cases h : i < N
  · rw [List.getD_eq_getElem _ _ (by simpa using h)]
    simpa only [pack, List.getElem_ofFn] using Function.extend_apply' (f := idx) w
      (fun _ => d) i (by simpa using hi)
  · exact List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt h)

/-- With an explicit list of occupied keys the packed list is computable. -/
def packFrom (xs : List α) (d : β) (idx : α → ℕ) (N : ℕ) (w : α → β) : List β :=
  List.ofFn fun i : Fin N => ((xs.find? fun x => idx x == i.val).map w).getD d

theorem packFrom_eq_pack (xs : List α) (d : β) (idx : α → ℕ) (N : ℕ) (w : α → β)
    (hxs : ∀ x, x ∈ xs) (hinj : Function.Injective idx) :
    packFrom xs d idx N w = pack d idx N w := by
  unfold packFrom pack
  congr 1
  funext i
  cases h : xs.find? (fun x => idx x == i.val) with
  | none =>
    have hi : ∀ x, idx x ≠ i.val := by
      intro x
      simpa using (List.find?_eq_none.mp h x (hxs x))
    exact (Function.extend_apply' w (fun _ => d) i.val (by simpa using hi)).symm
  | some x =>
    have hi : idx x = i.val := by simpa using List.find?_some h
    simp [← hi, hinj.extend_apply]

end FlatAtlas.PackingList

end NearSquareRoot
end Computability
end OAI

import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-! # Persistent identifiers for expert lists across trials

An entry is identified by its offset in the list. Equal representatives added in
different trials retain different offsets, as required by the fixed-share updates.
-/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Learning
namespace Catalog

/-- All additions in the first `t` trials, in their generation order. -/
def entries {α : Type*} (batch : ℕ → List α) : ℕ → List α
  | 0 => []
  | t+1 => entries batch t ++ batch t

theorem length_entries {α : Type*} (batch : ℕ → List α) (t : ℕ) :
    (entries batch t).length = ∑ i ∈ Finset.range t, (batch i).length := by
  induction t with
  | zero => simp [entries]
  | succ t ih => simp [entries,Finset.sum_range_succ,ih]

theorem length_mono {α : Type*} (batch : ℕ → List α) :
    Monotone (fun n => (entries batch n).length) := by
  apply monotone_nat_of_le_succ
  intro n
  simp [entries]

/-- The actual natural-number index that the newly appended entry receives. -/
def freshId {α : Type*} (batch : ℕ → List α) (t : ℕ) (j : Fin (batch t).length) : ℕ :=
  (entries batch t).length + j.val

theorem fresh_lt_length {α : Type*} (batch : ℕ → List α) (t : ℕ) (j : Fin (batch t).length) :
    freshId batch t j < (entries batch (t+1)).length := by
  simp [freshId,entries]

theorem stable_lookup {α : Type*} (batch : ℕ → List α) {s t i : ℕ} (hst : s ≤ t)
    (hi : i < (entries batch s).length) : (entries batch t)[i]? = (entries batch s)[i]? := by
  induction t, hst using Nat.le_induction with
  | base => rfl
  | succ t hst ih =>
    rw [entries,List.getElem?_append_left (hi.trans_le (length_mono _ hst)),ih]

theorem fresh_lookup {α : Type*} (batch : ℕ → List α) {s t : ℕ} (hst : s < t)
    (j : Fin (batch s).length) : (entries batch t)[freshId batch s j]? = some (batch s)[j.val] := by
  rw [stable_lookup batch hst (fresh_lt_length batch s j)]
  simp [entries,freshId]

theorem freshId_injective {α : Type*} (batch : ℕ → List α) (s : ℕ) :
    Function.Injective (freshId batch s) := by
  intro i j hij
  exact Fin.ext <| Nat.add_left_cancel hij

theorem freshId_order {α : Type*} (batch : ℕ → List α) {s t : ℕ} (hst : s < t)
    (i : Fin (batch s).length) (j : Fin (batch t).length) :
    freshId batch s i < freshId batch t j := by
  exact (fresh_lt_length batch s i).trans_le ((length_mono batch hst).trans (Nat.le_add_right ..))

theorem entries_size_bound {α : Type*} (batch : ℕ → List α) (t bound : ℕ)
    (hb : ∀ i < t, (batch i).length ≤ bound) : (entries batch t).length ≤ t*bound := by
  rw [length_entries]
  calc
    _ ≤ ∑ _ ∈ Finset.range t, bound := Finset.sum_le_sum fun i hi => hb i (Finset.mem_range.mp hi)
    _ = _ := by simp

end Catalog
end Learning
end PriceGame
end LinearProgramming
end Optimization
end OAI

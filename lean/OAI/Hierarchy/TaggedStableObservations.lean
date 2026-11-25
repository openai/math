import OAI.Hierarchy.TaggedRadixPack
import Mathlib.Data.List.Perm.Basic
import Mathlib.Tactic

namespace OAI
/-! # Stable order of real records through padded physical passes -/

namespace Hierarchy.Tagged.Radix
open scoped Classical
noncomputable section

variable {α κ : Type*}

private theorem observe_bucket [DecidableEq κ] (key : α → κ) (a : κ) {β : Type*}
    (read : α → Option β) (onlyKey : ∀ i, key i ≠ a → read i = none) (xs : List α) :
    (bucket key a xs).filterMap read = xs.filterMap read := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases ke : key x = a
    · have tail : (xs.filter fun y => decide (key y=a)).filterMap read=xs.filterMap read := ih
      cases out : read x <;> simp [bucket,ke,out,tail]
    · simp [bucket,ke,onlyKey x ke] at ih ⊢
      exact ih

/-- Stable tuple sorting preserves every partial reading confined to one key,
including reads which then discard additional inactive rows. -/
theorem stable_observe [LinearOrder κ] {n : ℕ} (key : Fin n → κ) (a : κ) (read : Fin n → Option α)
    (onlyKey : ∀ i, key i ≠ a → read i = none) :
    (List.ofFn (Tuple.sort key)).filterMap read = (List.ofFn id).filterMap read := by
  rw [← observe_bucket key a read onlyKey, stable_sort_bucket, observe_bucket]
  exact onlyKey

/-- A packed read returns the observations of its lanes in order.
Whole-pack stable sorting preserves each digit's lane sequence. -/
theorem stable_observe_packs [LinearOrder κ] {n : ℕ} (key : Fin n → κ) (a : κ)
    (read : Fin n → List α) (onlyKey : ∀ i, key i ≠ a → read i = []) :
    (List.ofFn (Tuple.sort key)).flatMap read = (List.ofFn id).flatMap read := by
  have restrict (xs : List (Fin n)) : (bucket key a xs).flatMap read = xs.flatMap read := by
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      by_cases ke : key x = a <;> simp [bucket, *] at *
  rw [← restrict, stable_sort_bucket, restrict]

/-- If each new digit bucket is exactly the corresponding old bucket, an
order on lower digits survives the next stable pass. -/
theorem refine_list_order {β : Type*} [LinearOrder κ] [LinearOrder β]
    (upper : α → κ) (lower : α → β) {old new : List α}
    (lo : old.Pairwise (fun x y => lower x ≤ lower y))
    (hi : new.Pairwise (fun x y => upper x ≤ upper y))
    (stable : ∀ a, bucket upper a new = bucket upper a old) :
    new.Pairwise (fun x y => toLex (upper x,lower x) ≤ toLex (upper y,lower y)) := by
  apply List.pairwise_iff_forall_sublist.mpr
  intro x y pair
  have weak := List.pairwise_iff_forall_sublist.mp hi pair
  rcases weak.lt_or_eq with lt|eq
  · exact Prod.Lex.toLex_le_toLex.mpr (Or.inl lt)
  · apply Prod.Lex.toLex_le_toLex.mpr
    refine Or.inr ⟨eq,?_⟩
    have selected : [x,y].Sublist (bucket upper (upper x) new) := by
      simpa [bucket,eq] using pair.filter (fun z => decide (upper z = upper x))
    rw [stable] at selected
    exact List.pairwise_iff_forall_sublist.mp (lo.sublist (List.filter_sublist ..)) selected

/-- Equal digit buckets preserve the full multiset, with repeated payloads. -/
theorem perm_of_buckets [DecidableEq κ] (key : α → κ) {old new : List α}
    (stable : ∀ a, bucket key a new = bucket key a old) : new.Perm old := by
  classical
  apply List.perm_iff_count.mpr
  intro x
  have keep (xs : List α) : (bucket key (key x) xs).count x = xs.count x := by
    induction xs with
    | nil => rfl
    | cons h xs ih =>
      by_cases eq : h=x
      · subst h; simp [bucket]
      · by_cases k : key h = key x <;> simp [bucket,k,eq]
  rw [← keep new,stable,keep]

end
end Hierarchy.Tagged.Radix

end OAI

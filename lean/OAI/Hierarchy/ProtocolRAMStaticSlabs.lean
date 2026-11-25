import Init.Data.List.FinRange
import Init.Data.List.Find
import Mathlib.Data.Fin.Basic

namespace OAI
/-! # One initial word tape for disjoint public controller slabs -/

namespace Hierarchy.ProtocolRAMStaticSlabs

/-- The endpoint on the right is exclusive. Empty ranges are permitted. -/
abbrev Inside {q : ℕ} (lo hi : Fin q → ℕ) (i : Fin q) (a : ℕ) : Prop :=
  lo i ≤ a ∧ a < hi i

def Disjoint {q : ℕ} (lo hi : Fin q → ℕ) : Prop :=
  ∀ i j a, Inside lo hi i a → Inside lo hi j a → i=j

/-- Sequential public enumeration gives an ordinary computable lookup. -/
def owner {q : ℕ} (lo hi : Fin q → ℕ) (a : ℕ) : Option (Fin q) :=
  (List.finRange q).find? (fun i => decide (Inside lo hi i a))

/-- All slab values can refer to their own separately assembled initial tape.
At addresses outside every slab the original tape is retained. -/
def mounted {A : Type*} {q : ℕ} (lo hi : Fin q → ℕ)
    (data : Fin q → ℕ → A) (raw : ℕ → A) (a : ℕ) : A :=
  match owner lo hi a with
  | some i => data i a
  | none => raw a

theorem owner_of_inside {q : ℕ} {lo hi : Fin q → ℕ} (separate : Disjoint lo hi)
    {i : Fin q} {a : ℕ} (hit : Inside lo hi i a) : owner lo hi a = some i := by
  cases h : owner lo hi a with
  | none =>
    unfold owner at h
    have miss := (List.find?_eq_none.mp h) i (List.mem_finRange i)
    exact False.elim (miss (by simpa using hit))
  | some j =>
    unfold owner at h
    have selected := List.find?_some (p := fun t : Fin q => decide (Inside lo hi t a)) h
    have found : Inside lo hi j a := of_decide_eq_true selected
    rw [separate j i a found hit]

theorem owner_outside {q : ℕ} {lo hi : Fin q → ℕ} {a : ℕ} (miss : ∀ i, ¬ Inside lo hi i a) :
    owner lo hi a = none := by
  unfold owner
  apply List.find?_eq_none.mpr
  intro i _
  simpa using miss i

theorem cell_on {A : Type*} {q : ℕ} {lo hi : Fin q → ℕ}
    (data : Fin q → ℕ → A) (raw : ℕ → A) (separate : Disjoint lo hi)
    {i : Fin q} {a : ℕ} (hit : Inside lo hi i a) : mounted lo hi data raw a = data i a := by
  simp [mounted,owner_of_inside separate hit]

theorem outside {A : Type*} {q : ℕ} {lo hi : Fin q → ℕ}
    (data : Fin q → ℕ → A) (raw : ℕ → A) {a : ℕ} (miss : ∀ i, ¬ Inside lo hi i a) :
    mounted lo hi data raw a = raw a := by simp [mounted,owner_outside miss]

/-- Monotone non-overlap is a convenient source of the pointwise disjointness
hypothesis for slabs scheduled in increasing physical address order. -/
theorem disjoint_of_order {q : ℕ} {lo hi : Fin q → ℕ}
    (before : ∀ i j, i<j → hi i ≤ lo j) : Disjoint lo hi := by
  intro i j a left right
  rcases Nat.lt_trichotomy i.val j.val with h|h|h
  · exact False.elim ((Nat.not_lt_of_ge (before i j h)) (Nat.lt_of_le_of_lt right.1 left.2))
  · exact Fin.ext h
  · exact False.elim ((Nat.not_lt_of_ge (before j i h)) (Nat.lt_of_le_of_lt left.1 right.2))


end Hierarchy.ProtocolRAMStaticSlabs

end OAI

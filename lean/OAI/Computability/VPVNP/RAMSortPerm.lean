import OAI.Computability.VPVNP.RAMSortNetwork
import Mathlib.Data.List.OfFn

/-!
# Record multiplicities in the bitonic network

Each comparator outputs its two inputs in one of the two orders. Consequently the
list of records in a whole block is permuted by the network, including repeated records.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMSort

variable {α : Type*}

/-- In wire order, joining two contiguous blocks concatenates their record lists. -/
theorem ofFn_join {b : ℕ} (x y : Wires b α) :
    List.ofFn (join x y) = List.ofFn x ++ List.ofFn y := by
  apply List.ext_getElem
  · rw [List.length_append, List.length_ofFn, List.length_ofFn, List.length_ofFn,
      Nat.pow_succ, Nat.mul_two]
  intro i hi hj
  rw [List.getElem_append]
  simp [List.getElem_ofFn, join]

private theorem ofFn_halves {b : ℕ} (x : Wires (b + 1) α) :
    List.ofFn (lo x) ++ List.ofFn (hi x) = List.ofFn x := by
  rw [← ofFn_join, join_lo_hi]

variable [LinearOrder α]

/-- A single parallel comparison layer preserves all input records. -/
theorem compare_perm {n : ℕ} (up : Bool) (x y : Fin n → α) :
    (List.ofFn (fun i ↦ lower up (x i) (y i)) ++ List.ofFn (fun i ↦ upper up (x i) (y i))).Perm
      (List.ofFn x ++ List.ofFn y) := by
  apply List.perm_iff_count.mpr
  intro a
  induction n with
  | zero => simp
  | succ n ih =>
    specialize ih (fun i ↦ x i.succ) (fun i ↦ y i.succ)
    simp only [List.count_append] at ih
    simp only [List.count_append, List.ofFn_succ, List.count_cons]
    let wt (z : α) : ℕ := if z == a then 1 else 0
    have heads : wt (lower up (x 0) (y 0)) + wt (upper up (x 0) (y 0)) = wt (x 0) + wt (y 0) := by
      rcases le_total (x 0) (y 0) with h | h
      · cases up <;> simp [lower, upper, min_eq_left h, max_eq_right h, Nat.add_comm]
      · cases up <;> simp [lower, upper, min_eq_right h, max_eq_left h, Nat.add_comm]
    dsimp [wt] at heads
    omega

/-- A merge phase preserves the multiset of records of the input block. -/
theorem merge_perm (b : ℕ) (up : Bool) (x : Wires b α) :
    (List.ofFn (merge b up x)).Perm (List.ofFn x) := by
  induction b with
  | zero => exact List.Perm.refl _
  | succ b ih =>
    rw [merge, ofFn_join, ← ofFn_halves x]
    exact ((ih _).append (ih _)).trans (compare_perm up (lo x) (hi x))

/-- The full network preserves every record and its multiplicity. -/
theorem sort_perm (b : ℕ) (up : Bool) (x : Wires b α) :
    (List.ofFn (sort b up x)).Perm (List.ofFn x) := by
  induction b generalizing up with
  | zero => exact List.Perm.refl _
  | succ b ih =>
    rw [sort]
    refine (merge_perm _ _ _).trans ?_
    rw [ofFn_join, ← ofFn_halves x]
    exact (ih true _).append (ih false _)

end RAMSort

end VPVNP
end Computability
end OAI

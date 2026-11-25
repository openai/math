import OAI.Hierarchy.GraphContractions

namespace OAI
/-! # Intersecting rooted regions in a tree decomposition -/

namespace Hierarchy.IncidenceGraph.TreeDecomposition

variable {G : IncidenceGraph} (D : G.TreeDecomposition)

/-- Every point of the region reaches its top along a parent path in the region. -/
def RootedRegion (P : D.Bag → Prop) (top : D.Bag) : Prop :=
  P top ∧ ∀ i, P i → ∃ k : ℕ, (D.parent^[k]) i = top ∧ ∀ j ≤ k, P ((D.parent^[j]) i)

private theorem parent_level_le (i : D.Bag) : D.level (D.parent i) ≤ D.level i := by
  by_cases hi : i = D.root
  · rw [hi, D.parent_root]
  · exact (D.parent_lt i hi).le

private theorem ancestor_level_le (i : D.Bag) (k : ℕ) :
    D.level ((D.parent^[k]) i) ≤ D.level i := by
  induction k generalizing i with
  | zero => exact le_rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    exact (ih (D.parent i)).trans (D.parent_level_le i)

private theorem ancestor_eq_of_level (i : D.Bag) (k : ℕ)
    (h : D.level i ≤ D.level ((D.parent^[k]) i)) : (D.parent^[k]) i = i := by
  cases k with
  | zero => rfl
  | succ k =>
    by_cases hi : i = D.root
    · rw [hi, Function.iterate_fixed D.parent_root]
    · rw [Function.iterate_succ_apply] at h
      exact (not_lt_of_ge (h.trans (D.ancestor_level_le (D.parent i) k)) (D.parent_lt i hi)).elim

/-- At an intersection the top with larger level belongs to the other region. -/
theorem region_intersection {P Q : D.Bag → Prop} {a b : D.Bag}
    (hP : D.RootedRegion P a) (hQ : D.RootedRegion Q b)
    (common : ∃ i, P i ∧ Q i) (level : D.level a ≤ D.level b) : P b := by
  obtain ⟨i, hiP, hiQ⟩ := common
  obtain ⟨m, hm, path⟩ := hP.2 i hiP
  obtain ⟨n, hn, _⟩ := hQ.2 i hiQ
  by_cases h : n ≤ m
  · rw [← hn]
    exact path n h
  · have hn' : (D.parent^[n-m]) a = b := by
      rw [← hm, ← Function.iterate_add_apply, Nat.sub_add_cancel (by omega : m ≤ n), hn]
    have same : b = a := by
      rw [← hn'] at level ⊢
      exact D.ancestor_eq_of_level a _ level
    rw [same]
    exact hP.1

private theorem region_union_top {P Q : D.Bag → Prop} {a b : D.Bag}
    (hP : D.RootedRegion P a) (hQ : D.RootedRegion Q b) (hb : P b) :
    D.RootedRegion (fun i => P i ∨ Q i) a := by
  refine ⟨Or.inl hP.1, ?_⟩
  intro i hi
  rcases hi with hi|hi
  · obtain ⟨k,hk,path⟩ := hP.2 i hi
    exact ⟨k,hk,fun j hj => Or.inl (path j hj)⟩
  · obtain ⟨n,hn,toB⟩ := hQ.2 i hi
    obtain ⟨m,hm,toA⟩ := hP.2 b hb
    refine ⟨m+n,by rw [Function.iterate_add_apply,hn,hm],?_⟩
    intro j hj
    by_cases first : j ≤ n
    · exact Or.inr (toB j first)
    · have eqn : (D.parent^[j]) i = (D.parent^[j-n]) b := by
        rw [←hn, ←Function.iterate_add_apply, Nat.sub_add_cancel (by omega : n ≤ j)]
      rw [eqn]
      exact Or.inl (toA (j-n) (by omega))

/-- Two overlapping regions are rooted at the shallower of their two tops. -/
theorem region_union {P Q : D.Bag → Prop} {a b : D.Bag}
    (hP : D.RootedRegion P a) (hQ : D.RootedRegion Q b) (common : ∃ i, P i ∧ Q i) :
    ∃ c, D.RootedRegion (fun i => P i ∨ Q i) c := by
  rcases le_total (D.level a) (D.level b) with h|h
  · exact ⟨a, D.region_union_top hP hQ (D.region_intersection hP hQ common h)⟩
  · have swapped : ∃ i, Q i ∧ P i := common.imp fun _ hit => hit.symm
    have region := D.region_union_top hQ hP (D.region_intersection hQ hP swapped h)
    have changeOrder : (fun i => Q i ∨ P i) = (fun i => P i ∨ Q i) :=
      funext fun _ => propext or_comm
    rw [changeOrder] at region
    exact ⟨b, region⟩


end Hierarchy.IncidenceGraph.TreeDecomposition

end OAI

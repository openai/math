import OAI.LinearAlgebra.MatrixExponent.Integral.Nodes

/-!
# Composition and costs of straight-line circuits
-/

namespace OAI.LinearAlgebra.MatrixExponent

variable {K : Type*} [CommRing K] {S S' T T' U : Set K} {m n : ℕ}

private theorem Integral.Build.retains (h : Integral.Build S m T) : S ⊆ T := by
  induction h with
  | nil => exact Set.Subset.rfl
  | add _ _ _ ih | sub _ _ _ ih | mul _ _ _ ih =>
    exact ih.trans (Set.subset_insert _ _)

/-- Replay a circuit after any computation making its inputs available. -/
private theorem Integral.Build.append (h : Integral.Build S m T) (g : Integral.Build T' n U) (ht : T' ⊆ T) :
    ∃ V, Integral.Build S (m + n) V ∧ U ⊆ V := by
  induction g with
  | nil => exact ⟨T, h, ht⟩
  | add _ hx hy ih =>
    obtain ⟨V, hV, hv⟩ := ih
    exact ⟨_, hV.add (hv hx) (hv hy), Set.insert_subset_insert hv⟩
  | sub _ hx hy ih =>
    obtain ⟨V, hV, hv⟩ := ih
    exact ⟨_, hV.sub (hv hx) (hv hy), Set.insert_subset_insert hv⟩
  | mul _ hx hy ih =>
    obtain ⟨V, hV, hv⟩ := ih
    exact ⟨_, hV.mul (hv hx) (hv hy), Set.insert_subset_insert hv⟩

/-- A cost bound on producing a set of values. The registers may contain
additional intermediate values. -/
def CanMake (S : Set K) (m : ℕ) (T : Set K) : Prop :=
  ∃ c ≤ m, ∃ U, Integral.Build S c U ∧ T ⊆ U

namespace CanMake

theorem of_subset (h : T ⊆ S) : CanMake S 0 T :=
  ⟨0, le_rfl, S, .nil, h⟩

theorem mono_cost (h : CanMake S m T) (hc : m ≤ n) : CanMake S n T := by
  obtain ⟨c, hc', V, hv, ht⟩ := h
  exact ⟨c, hc'.trans hc, V, hv, ht⟩

theorem mono_output (h : CanMake S m T) (ht : T' ⊆ T) : CanMake S m T' := by
  obtain ⟨c, hc, V, hv, ht'⟩ := h
  exact ⟨c, hc, V, hv, ht.trans ht'⟩

theorem trans (h : CanMake S m T) (g : CanMake T n U) : CanMake S (m + n) U := by
  obtain ⟨a, ha, A, hA, hT⟩ := h
  obtain ⟨b, hb, B, hB, hU⟩ := g
  obtain ⟨V, hV, hv⟩ := hA.append hB hT
  exact ⟨a + b, Nat.add_le_add ha hb, V, hV, hU.trans hv⟩

theorem mono_input (h : CanMake S m T) (hs : S ⊆ S') : CanMake S' m T := by
  simpa using (of_subset hs).trans h

theorem keep (h : CanMake S m T) : CanMake S m (S ∪ T) := by
  obtain ⟨c, hc, V, hv, ht⟩ := h
  exact ⟨c, hc, V, hv, Set.union_subset hv.retains ht⟩

theorem union (h : CanMake S m T) (g : CanMake S n U) : CanMake S (m + n) (T ∪ U) := by
  have g' : CanMake (S ∪ T) n U := g.mono_input Set.subset_union_left
  exact (h.keep.trans g'.keep).mono_output (Set.union_subset_union_left U Set.subset_union_right)

theorem iUnion {ι : Type*} [Fintype ι] {T : ι → Set K}
    (h : ∀ i, CanMake S m (T i)) : CanMake S (Fintype.card ι * m) (⋃ i, T i) := by
  classical
  have aux (s : Finset ι) : CanMake S (s.card * m) (⋃ i ∈ s, T i) := by
    induction s using Finset.induction_on with
    | empty => simpa using of_subset (Set.empty_subset S)
    | @insert i s hi ih =>
      rw [Finset.card_insert_of_notMem hi, Nat.add_mul, Nat.one_mul, add_comm]
      simpa using (h i).union ih
  simpa using aux Finset.univ

theorem range {ι : Type*} [Fintype ι] {f : ι → K}
    (h : ∀ i, CanMake S m {f i}) : CanMake S (Fintype.card ι * m) (Set.range f) := by
  refine (iUnion h).mono_output ?_
  rintro _ ⟨i, rfl⟩
  exact Set.mem_iUnion_of_mem i rfl

theorem mul {x y : K} (hx : x ∈ S) (hy : y ∈ S) : CanMake S 1 {x * y} :=
  ⟨1, le_rfl, _, Integral.Build.nil.mul hx hy, Set.singleton_subset_iff.mpr (Set.mem_insert _ _)⟩

theorem add {x y : K} (hx : x ∈ S) (hy : y ∈ S) : CanMake S 1 {x + y} :=
  ⟨1, le_rfl, _, Integral.Build.nil.add hx hy, Set.singleton_subset_iff.mpr (Set.mem_insert _ _)⟩

/-- Two operations per term suffice, including the first addition to zero. -/
theorem linear {ι : Type*} [Fintype ι] {a x : ι → K}
    (h0 : 0 ∈ S) (ha : ∀ i, a i ∈ S) (hx : ∀ i, x i ∈ S) :
    CanMake S (Fintype.card ι * 2) {∑ i, a i * x i} := by
  classical
  have aux (s : Finset ι) : CanMake S (s.card * 2) {∑ i ∈ s, a i * x i} := by
    induction s using Finset.induction_on with
    | empty => simpa using of_subset (Set.singleton_subset_iff.mpr h0)
    | @insert i s hi ih =>
      rw [Finset.card_insert_of_notMem hi, Nat.add_mul, Nat.one_mul, Finset.sum_insert hi]
      exact (ih.union (mul (ha i) (hx i))).trans (add (Or.inr rfl) (Or.inl rfl))
  exact aux Finset.univ

end CanMake
end OAI.LinearAlgebra.MatrixExponent

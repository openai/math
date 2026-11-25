import OAI.Hierarchy.BinaryTreeCore
import OAI.Hierarchy.GraphContractions

namespace OAI
/-! # Size, degree and treewidth of complete binary trees -/

namespace Hierarchy.BinaryTree

/-- The edges point from parent to child, with the root at height zero in the tree. -/
def graph (h : ℕ) : IncidenceGraph where
  V := V h
  E := E h
  left := left h
  right := right h
  loopless := left_ne_right h

/-- The edges at a vertex are its incoming edge and the two possible child edges. -/
theorem degree_le_three (h : ℕ) (v : (graph h).V) : (graph h).degree v ≤ 3 := by
  classical
  let code (e : (graph h).Incident v) : Option Bool :=
    if left h e.1=v then some (side h e.1) else none
  have injective : Function.Injective code := by
    intro e f same
    by_cases he : left h e.1=v <;> by_cases hf : left h f.1=v
    · exact Subtype.ext (left_side_injective h _ _ (he.trans hf.symm)
        (by
          exact Option.some.inj (by simpa only [code,ite_eq_left he,ite_eq_left hf] using same)))
    · simp only [code,ite_eq_left he,ite_eq_right hf] at same
      cases same
    · simp only [code,ite_eq_right he,ite_eq_left hf] at same
      cases same
    · have re : right h e.1=v := e.2.resolve_left he
      have rf : right h f.1=v := f.2.resolve_left hf
      exact Subtype.ext (right_injective h (re.trans rf.symm))
  simpa [IncidenceGraph.degree] using Fintype.card_le_of_injective code injective

private noncomputable def bag (h : ℕ) (v : V h) : Finset (V h) := by
  classical
  exact {v,parent h v}

private theorem mem_bag {h : ℕ} {v i : V h} : v∈bag h i ↔ v=i ∨ v=parent h i := by
  classical
  change v∈insert i {parent h i} ↔ _
  rw [Finset.mem_insert,Finset.mem_singleton]

/-- Index bags by vertices, and place each vertex in its own bag and its children's bags. -/
noncomputable def treeDecomposition (h : ℕ) : (graph h).TreeDecomposition where
  Bag := V h
  root := root h
  parent := parent h
  level := level h
  parent_root := parent_root h
  parent_lt := parent_lt h
  bag := bag h
  vertex_cover := by intro v; exact ⟨v, mem_bag.mpr (.inl rfl)⟩
  edge_cover := by
    intro e
    refine ⟨right h e, ?_, ?_⟩
    · exact mem_bag.mpr (.inr (parent_right h e).symm)
    · exact mem_bag.mpr (.inl rfl)
  running := by
    classical
    intro v
    refine ⟨v,mem_bag.mpr (.inl rfl),?_⟩
    intro i hi
    change v∈bag h i at hi
    rcases mem_bag.mp hi with rfl|eqn
    · refine ⟨0,rfl,?_⟩
      intro j hj
      obtain rfl := Nat.eq_zero_of_le_zero hj
      exact hi
    · refine ⟨1,eqn.symm,?_⟩
      intro j hj
      rcases (show j=0 ∨ j=1 by omega) with rfl|rfl
      · exact hi
      · exact mem_bag.mpr (.inl eqn)

theorem treewidth_one (h : ℕ) : (graph h).TreewidthAtMost 1 := by
  classical
  refine ⟨treeDecomposition h,fun v => ?_⟩
  change (insert v {parent h v} : Finset (V h)).card ≤ 1+1
  exact (Finset.card_insert_le _ _).trans (by simp)


end Hierarchy.BinaryTree

end OAI

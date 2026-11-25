import OAI.Hierarchy.BinaryTreeCore

namespace OAI
/-! # Edges outside a grandchild subtree of a complete binary tree -/

namespace Hierarchy.BinaryTree

/-- The two side bits identify one of the four grandchildren of the root. -/
def grandChild {h : ℕ} (d : Bool × Bool) (v : V h) : V (h+2) :=
  child d.1 (child d.2 v)

def grandEdge {h : ℕ} (d : Bool × Bool) (e : E h) : E (h+2) :=
  childEdge d.1 (childEdge d.2 e)

theorem grandChild_injective {h : ℕ} (d : Bool × Bool) :
    Function.Injective (grandChild (h := h) d) := by
  intro u v eqn
  exact (child_inj (child_inj eqn).2).2

private theorem children_edges {h : ℕ} {a b : Bool} {e f : E h}
    (eqn : childEdge a e = childEdge b f) : a=b ∧ e=f := Prod.mk.inj (Sum.inr.inj eqn)

theorem grandEdge_injective {h : ℕ} (d : Bool × Bool) :
    Function.Injective (grandEdge (h := h) d) := by
  intro e f eqn
  exact (children_edges (children_edges eqn).2).2

@[simp] theorem left_grandEdge {h : ℕ} (d : Bool × Bool) (e : E h) :
    left (h+2) (grandEdge d e) = grandChild d (left h e) := rfl

@[simp] theorem right_grandEdge {h : ℕ} (d : Bool × Bool) (e : E h) :
    right (h+2) (grandEdge d e) = grandChild d (right h e) := rfl

theorem grandEdge_not_mem_range {h : ℕ} {a c : Bool × Bool} (diff : a ≠ c) (e : E h) :
    grandEdge a e ∉ Set.range (grandEdge (h := h) c) := by
  rintro ⟨x, hx⟩
  have eqn : (c.1,c.2) = (a.1,a.2) := by
    have outer := children_edges hx
    exact Prod.ext outer.1 (children_edges outer.2).1
  exact diff eqn.symm

/-- If the endpoints of every edge agree in color, every vertex has the
root's color. -/
private theorem agree_root (h : ℕ) : ∀ (color : V h → Prop),
    (∀ e, color (left h e) ↔ color (right h e)) → ∀ v, color v ↔ color (root h) := by
  induction h with
  | zero =>
    intro color same v
    cases v
    rfl
  | succ h ih =>
    intro color same v
    rcases v with _ | ⟨c,v⟩
    · rfl
    · exact (ih (fun z => color (child c z)) (fun e => same (childEdge c e)) v).trans
        (same (rootEdge c)).symm

/-- Two opposite colors in grandchildren other than `c` force a crossing
outside the internal edge set of `c`. The two paths to the root use only
their own subtree edges and the edges incident to their two ancestors. -/
theorem crossing_outside {h : ℕ} (color : V (h+2) → Prop)
    {a b c : Bool × Bool} (ac : a ≠ c) (bc : b ≠ c) {u v : V h}
    (hu : color (grandChild a u)) (hv : ¬color (grandChild b v)) :
    ∃ e : E (h+2), ¬(color (left (h+2) e) ↔ color (right (h+2) e)) ∧
      e ∉ Set.range (grandEdge (h := h) c) := by
  classical
  by_contra missing
  have same (e : E (h+2)) (outside : e ∉ Set.range (grandEdge (h := h) c)) :
      color (left (h+2) e) ↔ color (right (h+2) e) := by
    by_contra differs
    exact missing ⟨e, differs, outside⟩
  have toRoot (d : Bool × Bool) (dc : d ≠ c) (x : V h) :
      color (grandChild d x) ↔ color (root (h+2)) := by
    have inTree := agree_root h (fun z => color (grandChild d z))
      (fun e => same (grandEdge d e) (grandEdge_not_mem_range dc e)) x
    have second := same (childEdge (h := h+1) d.1 (rootEdge d.2)) (by
      rintro ⟨e, he⟩
      have impossible : childEdge c.2 e = rootEdge d.2 := (children_edges he).2
      change (Sum.inr (c.2,e) : Bool ⊕ (Bool × E h)) = Sum.inl d.2 at impossible
      cases impossible)
    have first := same (rootEdge (h := h+1) d.1) (by
      rintro ⟨e, he⟩
      change (Sum.inr (c.1,childEdge c.2 e) : Bool ⊕ (Bool × E (h+1))) = Sum.inl d.1 at he
      cases he)
    exact inTree.trans (second.symm.trans first.symm)
  exact hv ((toRoot b bc v).mpr ((toRoot a ac u).mp hu))


end Hierarchy.BinaryTree

end OAI

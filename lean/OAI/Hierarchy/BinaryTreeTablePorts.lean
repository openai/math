import OAI.Hierarchy.BinaryTree
import OAI.Hierarchy.BinaryTreeSplit

namespace OAI
/-! # Restricting vertex-table arguments to one child of a binary tree -/

namespace Hierarchy.BinaryTree

/-- A subtree root has one additional argument for the color entering from its parent. -/
abbrev Port (h : ℕ) (v : V h) := (graph h).Incident v ⊕ PLift (v = root h)

def point {h q : ℕ} (z : E h → Fin q) (a : Fin q) (v : V h) : Port h v → Fin q :=
  Sum.elim (fun e => z e.val) (fun _ => a)

private theorem child_ne_root {h : ℕ} (s : Bool) (v : V h) : child s v ≠ root (h+1) := by
  intro eqn
  cases eqn

private theorem rootEdge_hit {h : ℕ} {s t : Bool} {v : V h}
    (hit : left (h+1) (rootEdge t) = child s v ∨ right (h+1) (rootEdge t) = child s v) :
    t=s ∧ root h=v := by
  rcases hit with eqn | eqn
  · exact ((child_ne_root s v) eqn.symm).elim
  · exact child_inj eqn

private theorem childEdge_hit {h : ℕ} {s t : Bool} {e : E h} {v : V h}
    (hit : left (h+1) (childEdge t e) = child s v ∨ right (h+1) (childEdge t e) = child s v) :
    t=s ∧ (left h e=v ∨ right h e=v) := by
  rcases hit with eqn | eqn
  · exact ⟨(child_inj (h:=h) eqn).1, Or.inl (child_inj (h:=h) eqn).2⟩
  · exact ⟨(child_inj (h:=h) eqn).1, Or.inr (child_inj (h:=h) eqn).2⟩

/-- In the child tree, the edge entering its root becomes its extra input port. -/
def childPort {h : ℕ} (s : Bool) (v : V h) : Port (h+1) (child s v) → Port h v
  | .inr extra => False.elim ((child_ne_root s v) extra.down)
  | .inl ⟨.inl t,hit⟩ => .inr ⟨(rootEdge_hit (h:=h) (s:=s) (t:=t) (v:=v) hit).2.symm⟩
  | .inl ⟨.inr (t,e),hit⟩ => .inl ⟨e,(childEdge_hit (h:=h) (s:=s) (t:=t) (e:=e) (v:=v) hit).2⟩

/-- On the root of a fork, the extra port and the two edges supply its three arguments. -/
def rootColors {h q : ℕ} (a i j : Fin q) : Port (h+1) (root (h+1)) → Fin q
  | .inr _ => a
  | .inl ⟨.inl false,_⟩ => i
  | .inl ⟨.inl true,_⟩ => j
  | .inl ⟨.inr (s,e),hit⟩ =>
    False.elim (hit.elim (child_ne_root s (left h e)) (child_ne_root s (right h e)))

theorem point_glue_root {h q : ℕ} (a i j : Fin q) (l r : E h → Fin q) :
    point (glueColor i j l r) a (root (h+1)) = rootColors a i j := by
  funext x
  rcases x with ⟨edge,hit⟩ | extra
  · rcases edge with t | ⟨s,e⟩
    · cases t <;> rfl
    · rcases hit with eqn | eqn
      · exact ((child_ne_root s (left h e)) eqn).elim
      · exact ((child_ne_root s (right h e)) eqn).elim
  · rfl

private theorem point_glue_child {h q : ℕ} (s : Bool) (a i j : Fin q) (l r : E h → Fin q) (v : V h) :
    point (glueColor i j l r) a (child s v) =
      point (if s then r else l) (if s then j else i) v ∘ childPort s v := by
  funext x
  rcases x with ⟨edge,hit⟩ | extra
  · rcases edge with t | ⟨t,e⟩
    · have eqn : t=s := (rootEdge_hit (h:=h) (s:=s) (t:=t) (v:=v) hit).1
      subst t
      cases s <;> rfl
    · have eqn : t=s := (childEdge_hit (h:=h) (s:=s) (t:=t) (e:=e) (v:=v) hit).1
      subst t
      cases s <;> rfl
  · exact ((child_ne_root s v) extra.down).elim

theorem point_glue_false {h q : ℕ} (a i j : Fin q) (l r : E h → Fin q) (v : V h) :
    point (glueColor i j l r) a (child false v) = point l i v ∘ childPort false v :=
  point_glue_child false a i j l r v

theorem point_glue_true {h q : ℕ} (a i j : Fin q) (l r : E h → Fin q) (v : V h) :
    point (glueColor i j l r) a (child true v) = point r j v ∘ childPort true v :=
  point_glue_child true a i j l r v

theorem point_leaf {q : ℕ} (z : E 0 → Fin q) (a : Fin q) : point z a (root 0) = fun _ => a := by
  funext x
  rcases x with ⟨e,_⟩ | extra
  · exact nomatch e
  · rfl

end Hierarchy.BinaryTree

end OAI

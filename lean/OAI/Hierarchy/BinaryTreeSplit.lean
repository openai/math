import OAI.Hierarchy.BinaryTreeCore
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi

namespace OAI
/-! # Splitting finite sums and products at the root of a binary tree -/

namespace Hierarchy.BinaryTree

open scoped BigOperators Classical

variable {h q : ℕ} {A : Type*}

/-- Assemble an edge coloring from the two root-edge colors and two subtree colorings. -/
def glueColor (i j : Fin q) (l r : E h → Fin q) : E (h+1) → Fin q
  | .inl false => i
  | .inl true => j
  | .inr (false,e) => l e
  | .inr (true,e) => r e

@[simp] theorem glueColor_root_false (i j : Fin q) (l r : E h → Fin q) :
    glueColor i j l r (rootEdge false) = i := rfl

@[simp] theorem glueColor_root_true (i j : Fin q) (l r : E h → Fin q) :
    glueColor i j l r (rootEdge true) = j := rfl

@[simp] theorem glueColor_child_false (i j : Fin q) (l r : E h → Fin q) (e : E h) :
    glueColor i j l r (childEdge false e) = l e := rfl

@[simp] theorem glueColor_child_true (i j : Fin q) (l r : E h → Fin q) (e : E h) :
    glueColor i j l r (childEdge true e) = r e := rfl

private def colorEquiv :
    (Fin q × Fin q × (E h → Fin q) × (E h → Fin q)) ≃ (E (h+1) → Fin q) where
  toFun x := glueColor x.1 x.2.1 x.2.2.1 x.2.2.2
  invFun a := (a (rootEdge false), a (rootEdge true),
    fun e => a (childEdge false e), fun e => a (childEdge true e))
  left_inv _ := rfl
  right_inv _ := by
    funext e
    rcases e with (b | ⟨b,e⟩) <;> cases b <;> rfl

/-- Sum over the four independent choices defining a coloring at a fork. -/
theorem sum_color_split [AddCommMonoid A] (z : (E (h+1) → Fin q) → A) :
    ∑ a, z a = ∑ i, ∑ j, ∑ l, ∑ r, z (glueColor i j l r) := by
  rw [← colorEquiv.sum_comp z]
  simp only [Fintype.sum_prod_type]; rfl

/-- Factor the vertex product into its root and its two subtree products. -/
theorem prod_vertex_split [CommMonoid A] (f : V (h+1) → A) :
    ∏ v, f v = f (root (h+1)) * (∏ v, f (child false v)) * (∏ v, f (child true v)) := by
  let g : Option (Bool × V h) → A := f
  change (∏ v : Option (Bool × V h), g v) =
    g none * (∏ v, g (some (false,v))) * (∏ v, g (some (true,v)))
  rw [Fintype.prod_option, Fintype.prod_prod_type, Fintype.prod_bool]
  ac_rfl

end Hierarchy.BinaryTree

end OAI

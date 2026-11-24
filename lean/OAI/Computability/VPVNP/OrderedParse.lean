import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma

/-!
# Finite ordered parses

A parse of layer `d` has `d + 1` terminal occurrences. At a binary production, the
split records the layer of the left child, and the two state labels specify the roots
of the child parses. The root state of the entire parse is supplied by the grammar.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace ParseGrammar

universe u v

/-- Ordered binary parse with terminal variables, child states and fixed leaf count. -/
inductive OrderedParse (V : Type u) (H : Type v) : ℕ → Type (max u v) where
  | leaf (v : V) : OrderedParse V H 0
  | node {d : ℕ} (b : Fin (d + 1)) (i j : H)
      (left : OrderedParse V H b.val) (right : OrderedParse V H (d - b.val)) :
      OrderedParse V H (d + 1)

namespace OrderedParse

variable {V : Type u} {H : Type v}

/-- A parse in degree one is determined by its sole terminal. -/
def leafEquiv : OrderedParse V H 0 ≃ V where
  toFun | leaf v => v
  invFun := leaf
  left_inv t := by cases t; rfl
  right_inv _ := rfl

/-- Decompose a binary parse into its split, child states and ordered subtrees. -/
def nodeEquiv (d : ℕ) : OrderedParse V H (d + 1) ≃
    Σ b : Fin (d + 1), H × H × OrderedParse V H b.val × OrderedParse V H (d - b.val) where
  toFun | node b i j left right => ⟨b, i, j, left, right⟩
  invFun | ⟨b, i, j, left, right⟩ => node b i j left right
  left_inv t := by cases t; rfl
  right_inv _ := rfl

instance instFintype [Fintype V] [Fintype H] : (d : ℕ) → Fintype (OrderedParse V H d)
  | 0 => Fintype.ofEquiv _ leafEquiv.symm
  | d + 1 => by
    letI (b : Fin (d + 1)) : Fintype (OrderedParse V H b.val) := instFintype b.val
    letI (b : Fin (d + 1)) : Fintype (OrderedParse V H (d - b.val)) := instFintype (d - b.val)
    exact Fintype.ofEquiv _ (nodeEquiv d).symm
termination_by d => d
decreasing_by
  · exact b.isLt
  · exact Nat.lt_succ_of_le (Nat.sub_le _ _)

/-- Terminal word, read from left to right with multiplicity. -/
def leaves {d : ℕ} : OrderedParse V H d → List V
  | leaf v => [v]
  | node _ _ _ left right => leaves left ++ leaves right

@[simp] theorem length_leaves {d : ℕ} (t : OrderedParse V H d) :
    t.leaves.length = d + 1 := by
  induction t with
  | leaf => rfl
  | node b _ _ _ _ ih₁ ih₂ =>
    rw [leaves, List.length_append, ih₁, ih₂]
    have := b.isLt
    omega

end OrderedParse
end ParseGrammar

end VPVNP
end Computability
end OAI

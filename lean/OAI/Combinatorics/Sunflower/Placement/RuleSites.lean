import OAI.Combinatorics.Sunflower.Rules
import OAI.Combinatorics.Sunflower.Placement.Sites
import Mathlib.Basic.Real.Basic

/-! # Source and target sites of an anchor rule -/

namespace OAI
namespace Combinatorics
namespace Sunflower
namespace Placement

variable {n : ℕ} {q : Rule (Fin (n + 2))}

/-- The three groups of locally readable sites for one ordered rule. -/
structure RuleSites {n : ℕ} (q : Rule (Fin (n + 2))) where
  L : Finset (Site n)
  R : Finset (Site n)
  T : Finset (Site n)
  hL : L.Nonempty
  hR : R.Nonempty
  hT : T.Nonempty
  left_sub : L ⊆ fiber q.left
  right_sub : R ⊆ fiber q.right
  target_sub : T ⊆ fiber q.target

namespace RuleSites

variable (d : RuleSites q)

/-- An equality filter at positive gap or a width-preserving copy to one target. -/
def Works (w : Finset (Site n) → ℝ) : Prop :=
  0 < w (d.L ∪ d.R) + w d.T - w ((d.L ∪ d.R) ∪ d.T) ∨
    ∃ s, d.T = {s} ∧ w (insert s (d.L ∪ d.R)) = w (d.L ∪ d.R)

theorem disjoint (hlt : q.left ≠ q.target) (hrt : q.right ≠ q.target) :
    Disjoint (d.L ∪ d.R) d.T := by
  refine Finset.disjoint_left.mpr ?_
  intro x hx ht
  have he := mem_fiber.mp (d.target_sub ht)
  rcases Finset.mem_union.mp hx with h | h
  · exact hlt ((mem_fiber.mp (d.left_sub h)).symm.trans he)
  · exact hrt ((mem_fiber.mp (d.right_sub h)).symm.trans he)

theorem antecedent_const {α : Type*} (f : Fin (n + 2) → α) (h : f q.left = f q.right) :
    ∀ s ∈ d.L ∪ d.R, f (group s) = f q.left := by
  intro s hs
  rcases Finset.mem_union.mp hs with hL | hR
  · rw [mem_fiber.mp (d.left_sub hL)]
  · rw [mem_fiber.mp (d.right_sub hR), h]

theorem target_const {α : Type*} (f : Fin (n + 2) → α) :
    ∀ s ∈ d.T, f (group s) = f q.target :=
  fun _ hs => congrArg f (mem_fiber.mp (d.target_sub hs))

theorem works_normalize {w v : Finset (Site n) → ℝ} {D : ℝ} (hD : 0 < D)
    (h : ∀ s : Finset (Site n), s.Nonempty → v s = w s / D)
    (hw : d.Works w) : d.Works v := by
  have hp := d.hL.mono (Finset.subset_union_left (s₂ := d.R))
  rcases hw with hg | ⟨s, hs, he⟩
  · left
    rw [h _ hp, h _ d.hT, h _ (hp.mono Finset.subset_union_left), ← add_div, ← sub_div]
    exact div_pos hg hD
  · right
    exact ⟨s, hs, by rw [h _ (Finset.insert_nonempty ..), he, h _ hp]⟩

end RuleSites

end Placement
end Sunflower
end Combinatorics
end OAI

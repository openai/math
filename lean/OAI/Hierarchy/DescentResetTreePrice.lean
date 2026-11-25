import OAI.Hierarchy.DescentBadBundles
import OAI.Hierarchy.DescentContactLinks

namespace OAI
/-! # Physical widths of both relay trees and the intervening reset contact cable -/

noncomputable section

namespace Hierarchy.DescentContactTree

open scoped Classical BigOperators

variable {I C : Type*} [Fintype I] [Fintype C]

/-- Installed widths of every relay edge at either endpoint and of the link
joining the two contact directories. -/
def treeEdgeCost (contact : I → C) (wt : I → ℕ) (l r : I → ℕ → Bool) (s t : ℕ) : ℕ :=
  (∑ d ∈ Finset.range (s+1), ∑ v : Node d, ∑ i : Cell l d v, wt i.val) +
    (∑ c : C, ∑ i : {i // contact i=c}, wt i.val) +
    (∑ d ∈ Finset.range (t+1), ∑ v : Node d, ∑ i : Cell r d v, wt i.val)

theorem treeEdgeCost_eq (contact : I → C) (wt : I → ℕ) (l r : I → ℕ → Bool) (s t : ℕ) :
    treeEdgeCost contact wt l r s t = (s+t+3)*(∑ i, wt i) :=
  two_tree_cost contact wt l r s t

end Hierarchy.DescentContactTree

namespace Hierarchy.DescentColonies

open DescentGL DescentBaseVariance DescentContactTree
open scoped Classical BigOperators

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] {k : ℕ}

/-- Each old wire is routed through fallback once if at least one of its two
actual sockets is in a marked base. -/
def badEdgeSet (b : V → ℕ) (hk : ∀v, b v≤k) (L : Layout k)
    (left right : E → V×Block k) (keys : Finset (V×ℕ)) : Finset E :=
  Finset.univ.filter fun e =>
    label b (baseOf b hk L (left e))∈keys ∨ label b (baseOf b hk L (right e))∈keys

theorem priced_badTreePrice_le {C : Type*} [Fintype C]
    (b : V → ℕ) (hk : ∀v, b v≤k) (L : Layout k)
    (left right : E → V×Block k) (width : E → ℕ) (price : ℝ) (hp : 0 ≤ price)
    (weight : V → Block k → ℝ)
    (inc : ∀ p, load left (fun e => price * (width e : ℝ)) p +
      load right (fun e => price * (width e : ℝ)) p ≤ weight p.1 p.2)
    (keys : Finset (V×ℕ)) (contact : ↥(badEdgeSet b hk L left right keys) → C)
    (l r : ↥(badEdgeSet b hk L left right keys) → ℕ → Bool) (s t : ℕ) :
    price * (treeEdgeCost contact (fun e => width e.val) l r s t : ℝ) ≤
      ((s+t+3 : ℕ):ℝ) * ∑ p ∈ validBases b keys, baseValue b hk weight L p := by
  have charged : (∑ e : ↥(badEdgeSet b hk L left right keys),price*(width e.val:ℝ)) ≤
      ∑ p ∈ validBases b keys, baseValue b hk weight L p := by
    have volume := exceptional_core b hk L left right (fun e => price*(width e:ℝ)) weight
      (fun e => mul_nonneg hp (Nat.cast_nonneg _)) inc keys
    calc
      _ = ∑ e ∈ badEdgeSet b hk L left right keys, price * (width e : ℝ) :=
        Finset.sum_coe_sort _ (fun e : E => price * (width e : ℝ))
      _ ≤ _ := by simpa only [badEdgeSet, Finset.sum_filter] using volume
  calc
    _ = ((s+t+3:ℕ):ℝ) * ∑ e : ↥(badEdgeSet b hk L left right keys),price*(width e.val:ℝ) := by
      rw [treeEdgeCost_eq,Nat.cast_mul,Nat.cast_sum,←Finset.mul_sum]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left charged (Nat.cast_nonneg _)

theorem badTreePrice_le {C : Type*} [Fintype C]
    (b : V → ℕ) (hk : ∀v, b v≤k) (L : Layout k)
    (left right : E → V×Block k) (width : E → ℕ) (weight : V → Block k → ℝ)
    (inc : ∀ p, load left (fun e => (width e : ℝ)) p + load right (fun e => (width e : ℝ)) p
      ≤ weight p.1 p.2)
    (keys : Finset (V×ℕ)) (contact : ↥(badEdgeSet b hk L left right keys) → C)
    (l r : ↥(badEdgeSet b hk L left right keys) → ℕ → Bool) (s t : ℕ) :
    (treeEdgeCost contact (fun e => width e.val) l r s t : ℝ) ≤
      ((s+t+3 : ℕ):ℝ) * ∑ p ∈ validBases b keys, baseValue b hk weight L p := by
  simpa only [one_mul] using priced_badTreePrice_le b hk L left right width 1 zero_le_one weight
    (by simpa only [one_mul] using inc) keys contact l r s t

/-- Secondary cables on old tether edges are paid separately from the exceptional
core. The two kinds of cables may use distinct contact catalogs and tree heights. -/
theorem treePrices_le {C T TC : Type*} [Fintype C] [Fintype T] [Fintype TC]
    (b : V → ℕ) (hk : ∀v, b v≤k) (L : Layout k)
    (left right : E → V×Block k) (width : E → ℕ) (weight : V → Block k → ℝ)
    (inc : ∀ p, load left (fun e => (width e : ℝ)) p + load right (fun e => (width e : ℝ)) p
      ≤ weight p.1 p.2)
    (keys : Finset (V×ℕ)) (contact : ↥(badEdgeSet b hk L left right keys) → C)
    (l r : ↥(badEdgeSet b hk L left right keys) → ℕ → Bool) (s t : ℕ)
    (tether : T → TC) (tetherWidth : T → ℕ) (l' r' : T → ℕ → Bool) (s' t' : ℕ) :
    ((treeEdgeCost contact (fun e => width e.val) l r s t +
      treeEdgeCost tether tetherWidth l' r' s' t' : ℕ) : ℝ) ≤
      ((s+t+3 : ℕ):ℝ) * (∑ p ∈ validBases b keys, baseValue b hk weight L p) +
        ((s'+t'+3 : ℕ):ℝ) * ((∑ i, tetherWidth i : ℕ) : ℝ) := by
  rw [Nat.cast_add,treeEdgeCost_eq tether,Nat.cast_mul]
  exact add_le_add (badTreePrice_le b hk L left right width weight inc keys contact l r s t) le_rfl

end Hierarchy.DescentColonies

end
end OAI

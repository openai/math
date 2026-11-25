import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.PlanarTreeNames

/-! # Certifying totals and preorder labels by parent and child equations

A parent map with strictly decreasing depth at every nonroot gives two
well-founded recursions. Totals are computed from the leaves upward and
preorder labels from the root downward. The root's total counts the
contribution of each vertex exactly once.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace PlanarPatch

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Children of a vertex exclude the root regardless of its stored parent. -/
def treeChildren (r : V) (parent : V → V) (v : V) : Finset V :=
  univ.filter fun w => w ≠ r ∧ parent w = v

/-- Each reported subtree total is the local contribution plus the child totals. -/
def SubtreeTotals (r : V) (parent : V → V) (weight total : V → ℕ) : Prop :=
  ∀ v, total v = weight v + ∑ w ∈ treeChildren r parent v, total w

/-- All subtree equations have a unique simultaneous solution. Strict descent
toward the root is enough; the stored parent of the root is never consulted. -/
theorem existsUnique_subtreeTotals (r : V) (parent : V → V) (depth weight : V → ℕ)
    (hdepth : ∀ v, v ≠ r → depth (parent v) < depth v) :
    ∃! total, SubtreeTotals r parent weight total := by
  let rank (v : V) := (∑ w, depth w) - depth v
  have less {v w : V} (hw : w ∈ treeChildren r parent v) : rank w < rank v := by
    obtain ⟨hne, he⟩ := (mem_filter.mp hw).2
    have hlt := hdepth w hne
    rw [he] at hlt
    have hle : depth w ≤ ∑ x, depth x := single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ w)
    dsimp [rank]
    omega
  let wf := (measure rank).wf
  let total : V → ℕ := wf.fix fun v ih =>
    weight v + ∑ w : treeChildren r parent v, ih w.val (less w.property)
  have ht : SubtreeTotals r parent weight total := by
    intro v
    dsimp only [total]
    rw [WellFounded.fix_eq]
    exact congrArg (weight v + ·) (sum_coe_sort _ _)
  refine ⟨total, ht, fun t ht' => funext fun v => ?_⟩
  induction v using wf.induction with
  | h v ih =>
    rw [ht' v, ht v]
    exact congrArg (weight v + ·) (sum_congr rfl (fun _ h => ih _ (less h)))

/-- Summing the equations charges every nonroot total once at its parent.
Cancellation leaves exactly the root total. -/
theorem root_total_eq_sum {r : V} {parent : V → V} {weight total : V → ℕ}
    (ht : SubtreeTotals r parent weight total) : total r = ∑ v, weight v := by
  have hchildren (v : V) : treeChildren r parent v = (univ.erase r).filter (parent · = v) := by
    ext w
    simp [treeChildren]
  have h := congrArg (fun t : V → ℕ => ∑ v, t v) (funext ht)
  change ∑ v, total v = ∑ v, (weight v + ∑ w ∈ treeChildren r parent v, total w) at h
  simp only [sum_add_distrib, hchildren, sum_fiberwise] at h
  have := sum_erase_add univ total (mem_univ r)
  omega

/-- Unit local contributions count the vertices at the root. -/
theorem root_subtreeSize_eq_card {r : V} {parent : V → V} {size : V → ℕ}
    (hs : SubtreeTotals r parent (fun _ => 1) size) : size r = Fintype.card V := by
  simpa using root_total_eq_sum hs

/-- The root is numbered one. Each child's name skips the parent and all
subtrees at earlier parent-side slots. -/
def PreorderNames (r : V) (parent : V → V) (slot size name : V → ℕ) : Prop :=
  name r = 1 ∧ ∀ w, w ≠ r → name w = name (parent w) + 1 +
    ∑ u ∈ (treeChildren r parent (parent w)).filter (fun u => slot u < slot w), size u

/-- The downward preorder equations have a unique solution for fixed sizes
and parent-side port order. -/
theorem existsUnique_preorderNames (r : V) (parent : V → V) (depth slot size : V → ℕ)
    (hdepth : ∀ v, v ≠ r → depth (parent v) < depth v) :
    ∃! name, PreorderNames r parent slot size name := by
  let offset (w : V) := ∑ u ∈ (treeChildren r parent (parent w)).filter (fun u => slot u < slot w), size u
  let wf := (measure depth).wf
  let name : V → ℕ := wf.fix fun v ih =>
    if h : v = r then 1 else ih (parent v) (hdepth v h) + 1 + offset v
  have eqn (v : V) : name v = if v = r then 1 else name (parent v) + 1 + offset v := by
    dsimp only [name]
    rw [WellFounded.fix_eq]
    split <;> simp_all
  have hn : PreorderNames r parent slot size name :=
    ⟨by simpa using eqn r, fun w hw => by simpa [hw, offset] using eqn w⟩
  refine ⟨name, hn, fun f hf => funext fun v => ?_⟩
  induction v using wf.induction with
  | h v ih =>
    by_cases hv : v = r
    · subst v; exact hf.1.trans hn.1.symm
    rw [hf.2 v hv, hn.2 v hv, ih (parent v) (hdepth v hv)]

end PlanarPatch

end SpectralBooks
end LinearAlgebra
end OAI

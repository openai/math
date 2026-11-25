import OAI.Computability.NearSquareRoot.PhysicalWalshOpen
import Mathlib.Data.Finset.Lattice.Fold

/-! # Bounding a closed command on fibres with finite physical boundaries -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.ClosedRuns

open IntegerMultiplication Code Space

/-- A finite collection containing all Boolean trees with at most `n` nodes. -/
private def trees : ℕ → Finset Tree
  | 0 => ∅
  | n+1 => {.atom false,.atom true} ∪ ((trees n) ×ˢ (trees n)).image (fun p => .fork p.1 p.2)

private theorem mem_trees {q : Tree} {n : ℕ} (h : q.count ≤ n) : q ∈ trees n := by
  induction n generalizing q with
  | zero => have := Tree.count_pos q; omega
  | succ n ih =>
    cases q with
    | atom b => cases b <;> simp [trees]
    | fork a b =>
      have ha := Tree.count_pos a
      have hb := Tree.count_pos b
      change a.count+b.count+1 ≤ n+1 at h
      exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨(a,b),Finset.mem_product.mpr ⟨ih (by omega : a.count ≤ n), ih (by omega : b.count ≤ n)⟩,rfl⟩)

/-- Every boundary pair can use the trace of one representative, even when
the calling index contains infinite data. A maximum over pairs of bounded
trees consequently gives a time and space bound depending only on `f x`. -/
theorem priceBy {X Y : Type*} {c : Cmd} {time space : X → ℕ} {q r : X → Tree}
    (h : ClosedRuns c time space q r) (f : X → Y) (V : Y → ℕ)
    (hv : ∀ x, max (q x).count (r x).count ≤ V (f x)) :
    ∃ bound : Y → ℕ, ClosedRuns c (bound ∘ f) (bound ∘ f) q r := by
  classical
  let present (p : Tree × Tree) := ∃ x : X, (q x,r x) = p
  let cost (p : Tree × Tree) := if e : present p then
    max (time (Classical.choose e)) (space (Classical.choose e)) else 0
  let bound y := (trees (V y) ×ˢ trees (V y)).sup cost
  obtain ⟨C,run⟩ := h
  refine ⟨bound,C,?_⟩
  intro x env parked base hp
  have e : present (q x,r x) := ⟨x,rfl⟩
  let y := Classical.choose e
  have pair : (q y,r y) = (q x,r x) := Classical.choose_spec e
  have hx := hv x
  have hc : cost (q x,r x) ≤ bound (f x) := Finset.le_sup (f := cost)
    (Finset.mem_product.mpr ⟨mem_trees (le_trans (le_max_left ..) hx),mem_trees (le_trans (le_max_right ..) hx)⟩)
  simp only [cost,dite_eq_left e] at hc
  have ht := Nat.mul_le_mul_left C (Nat.succ_le_succ (le_trans (le_max_left ..) hc))
  have hs := Nat.mul_le_mul_left C (Nat.succ_le_succ (le_trans (le_max_right ..) hc))
  have out := (run y env parked base hp).mono ht (Nat.add_le_add_left hs base) hs
  simpa only [(Prod.mk.inj pair).1,(Prod.mk.inj pair).2,Function.comp_apply,Nat.succ_eq_add_one] using out

end PhysicalWalsh.ClosedRuns

end NearSquareRoot
end Computability
end OAI

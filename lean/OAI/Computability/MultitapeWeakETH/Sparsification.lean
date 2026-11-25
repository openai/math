import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSCompletedTree
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Variable-count sparsification estimates for Middle, Theorem 3.2

Use the repository's disjoint counting traversal with arbitrary reciprocal
budget s. A sparse leaf operation still needs its characteristic-zero Port
implementation and a bit-time analysis.
-/

namespace OAI.Computability.MultitapeWeakETH

open OAI.Algorithms.SubexponentialSAT
open SqrtLogSpace SqrtLogSpace.DisjointReuse SparseDFSRefinement

/-- For width three the threshold chosen for budget 1/s gives O(s⁴)
occurrences per variable and at most poly(v,s) 2^(v/s) visits. -/
theorem disjoint_sparsification_bounds :
    ∃ K : ℕ, ∀ (s : ℕ) (hs : 0 < s),
      let M := SparseBudget.chooseM 3 1 s (by decide)
      (∀ {v} (F : SAT.CNF (Fin v)), SAT.WidthAtMost 3 F →
        SparsePriority.select F M = none → ∀ x, SAT.occurrences x F ≤ 4*K^2*s^4) ∧
      (∀ {v visits total : ℕ} {F : RawCNF v}, Valid 3 F →
        Transitions 3 M visits ⟨[⟨F,0⟩],0⟩ ⟨[],total⟩ →
        (visits:ℝ) ≤ ((24*K*s^2*v + 1 : ℕ) : ℝ)^2 * (2:ℝ)^((v:ℝ)/s)) := by
  obtain ⟨K,T,control⟩ := SparseBudget.choose_encoding_bounds 3
  refine ⟨K,fun s hs => ?_⟩
  let M := SparseBudget.chooseM 3 1 s (by decide)
  have small : M ≤ K*s^2 := (control 1 s (by decide) hs).1
  have two : 2 ≤ M := (SparseBudget.chooseM_spec 3 1 s (by decide)).1
  constructor
  · intro v F width terminal x
    have occ := SparseBudget.leaf_occurrences_le_power F 3 M (by decide) two width terminal x
    calc
      SAT.occurrences x F ≤ 4*M^2 := occ
      _ ≤ 4*(K*s^2)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left small 2)
      _ = _ := by ring
  · intro v visits total F valid history
    have depth : SparseCharging.depthConstant 3 M ≤ 24*M := by
      simpa using SparseBudget.depthConstant_le 3 M two
    have d : SparseCharging.depthConstant 3 M ≤ 24*K*s^2 :=
      depth.trans (by simpa only [mul_assoc] using Nat.mul_le_mul_left 24 small)
    apply (DFSCompletedTree.completed_visits_reciprocal 3 s (by decide) hs valid history).trans
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _)
      (Nat.cast_le.mpr (Nat.add_le_add_right (Nat.mul_le_mul_right v d) 1)) 2) (by positivity)

/-- Selecting s of order v^θ preserves a fixed power saving both for the tree
and for contraction of a leaf with O(v s⁴) occurrences. -/
theorem sparsification_exponents {δ : ℝ} (positive : 0 < δ) (small : δ < 1) :
    ∃ θ η : ℝ, 0 < θ ∧ 0 < η ∧ η < 1 ∧
      1-θ ≤ 1-η ∧ (1+4*θ)*(1-δ) ≤ 1-η := by
  refine ⟨δ/8,δ/8,by positivity,by positivity,by linarith,le_rfl,?_⟩
  nlinarith [sq_nonneg δ]

end OAI.Computability.MultitapeWeakETH

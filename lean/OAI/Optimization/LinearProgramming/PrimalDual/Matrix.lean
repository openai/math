import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sum
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Pi
import Mathlib.Tactic.Linarith

/-! The joint primal–dual feasibility system in the proof of Corollary 1.2. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PrimalDual

variable {K : Type*}

open Matrix
open scoped BigOperators

variable {I J K : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The five blocks index primal inequalities, positivity of the dual variables,
upper and lower bounds on each dual equation, and the duality gap. -/
abbrev JointRow (I J : Type*) := I ⊕ I ⊕ J ⊕ J ⊕ Unit

/-- Matrix of the joint system on the variables `(x, y)`. -/
def jointMatrix (A : Matrix I J K) (b : I → K) (c : J → K) : Matrix (JointRow I J) (J ⊕ I) K
  | .inl i => Sum.elim (A i) (fun _ => 0)
  | .inr (.inl i) => Sum.elim (fun _ => 0) (fun k => if k = i then -1 else 0)
  | .inr (.inr (.inl j)) => Sum.elim (fun _ => 0) (fun i => A i j)
  | .inr (.inr (.inr (.inl j))) => Sum.elim (fun _ => 0) (fun i => -A i j)
  | .inr (.inr (.inr (.inr _))) => Sum.elim (fun j => -c j) b

/-- Right-hand side of the joint system, in the same block order. -/
def jointRhs (b : I → K) (c : J → K) : JointRow I J → K :=
  Sum.elim b (Sum.elim (fun _ => 0) (Sum.elim c (Sum.elim (-c) (fun _ => 0))))

omit [DecidableEq I] in
/-- Number of inequalities of the second call. -/
theorem card_joint_rows : Fintype.card (JointRow I J) = 2 * Fintype.card I + 2 * Fintype.card J + 1 := by
  simp [JointRow]; omega

/-- Splitting the columns and the five row blocks recovers the primal and dual constraints. -/
theorem joint_feasible_iff (A : Matrix I J K) (b : I → K) (c : J → K) (z : J ⊕ I → K) :
    jointMatrix A b c *ᵥ z ≤ jointRhs b c ↔
      A *ᵥ (z ∘ Sum.inl) ≤ b ∧ 0 ≤ z ∘ Sum.inr ∧ Aᵀ *ᵥ (z ∘ Sum.inr) = c ∧
      b ⬝ᵥ (z ∘ Sum.inr) ≤ c ⬝ᵥ (z ∘ Sum.inl) := by
  simp only [Pi.le_def, Sum.forall, jointMatrix, jointRhs, Matrix.mulVec,
    dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Function.comp_apply,
    Pi.zero_apply, Pi.neg_apply, Matrix.transpose_apply, funext_iff, ite_mul, one_mul,
    zero_mul, neg_mul, Finset.sum_const_zero, Finset.sum_neg_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, add_zero, zero_add,
    neg_nonpos, neg_le_neg_iff]
  constructor
  · rintro ⟨hp, hn, hupper, hlower, hgap⟩
    exact ⟨hp, hn, fun j => le_antisymm (hupper j) (hlower j), by linarith [hgap ()]⟩
  · rintro ⟨hp, hn, heq, hgap⟩
    exact ⟨hp, hn, fun j => (heq j).le, fun j => (heq j).ge, fun _ => by linarith⟩

/-- The difference of the two nonnegative multipliers on the dual equation. -/
def equationMultiplier (s : JointRow I J → K) (j : J) : K :=
  s (.inr (.inr (.inl j))) - s (.inr (.inr (.inr (.inl j))))

/-- Column annihilation and the negative right-hand-side dot product of an augmented
Farkas certificate imply the three multiplier identities in the reduction. -/
theorem joint_certificate (A : Matrix I J K) (b : I → K) (c : J → K) (s : JointRow I J → K)
    (hz : (jointMatrix A b c)ᵀ *ᵥ s = 0) (hneg : jointRhs b c ⬝ᵥ s < 0) :
    let θ := s (.inr (.inr (.inr (.inr ()))))
    Aᵀ *ᵥ (s ∘ Sum.inl) = θ • c ∧
    A *ᵥ equationMultiplier s + θ • b = s ∘ Sum.inr ∘ Sum.inl ∧
    b ⬝ᵥ (s ∘ Sum.inl) + c ⬝ᵥ equationMultiplier s < 0 := by
  dsimp only
  have h := congrFun hz
  constructor
  · funext j
    specialize h (.inl j)
    simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, jointMatrix] at h
    change (∑ i, A i j * s (.inl i)) = _
    simpa [Pi.smul_apply, smul_eq_mul, mul_comm] using eq_of_sub_eq_zero (show
      (∑ i, A i j * s (.inl i)) - c j * s (.inr (.inr (.inr (.inr ())))) = 0 by linarith)
  constructor
  · funext i
    specialize h (.inr i)
    simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, jointMatrix, ite_mul] at h
    simp [Matrix.mulVec, dotProduct, equationMultiplier, mul_sub, Finset.sum_sub_distrib,
      Function.comp_apply, mul_comm] at h ⊢
    linarith
  · simpa [jointRhs, dotProduct, Fintype.sum_sum_type, equationMultiplier, mul_sub,
      mul_add, mul_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib, Function.comp_apply, sub_eq_add_neg, add_assoc] using hneg

end PrimalDual
end LinearProgramming
end Optimization
end OAI

import OAI.LinearAlgebra.FiniteFourier.Swap
import Mathlib.LinearAlgebra.Matrix.Rank
import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensor

/-! # The two collapsed rectangles of a controlled phase

At height zero the two copies of each register are at the same site, so
its flattening is the original matrix on the two diagonal subspaces. At
width zero it is a diagonal matrix indexed by pairs of register values.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section
open scoped Classical

variable {O I K : Type*} [Field K]

/-- The four-leg coefficient with its output pair and input pair written
separately. The left label is repeated at both left sites, and the right
label is repeated at both right sites. -/
def phaseEntry (M : Matrix O I K) (x : O) (y : I) (x' : O) (y' : I) : K :=
  if x = x' ∧ y = y' then M x y else 0

/-- Width zero groups both input legs and both output legs. -/
def phaseWidthZero (M : Matrix O I K) : Matrix (O × I) (O × I) K :=
  fun p q ↦ phaseEntry M p.1 p.2 q.1 q.2

/-- Height zero groups the two left legs and the two right legs. -/
def phaseHeightZero (M : Matrix O I K) : Matrix (O × O) (I × I) K :=
  fun p q ↦ phaseEntry M p.1 q.1 p.2 q.2

theorem phaseWidthZero_eq_diagonal (M : Matrix O I K) :
    phaseWidthZero M = Matrix.diagonal (fun p ↦ M p.1 p.2) := by
  ext p q
  simp [phaseWidthZero, phaseEntry, Matrix.diagonal, Prod.ext_iff]

/-- The grouped phase matrix acts as the controlled phase used in the
weighted-swap construction. -/
theorem phaseWidthZero_mulVec [Fintype O] (M : Matrix O O K) (v : O × O → K) :
    (phaseWidthZero M).mulVec v = controlledPhase M v := by
  funext p
  rw [phaseWidthZero_eq_diagonal, Matrix.mulVec_diagonal]
  rfl

variable [Fintype O] [Fintype I]

/-- At zero width the two-site flattening rank counts all nonzero entries. -/
theorem rank_phaseWidthZero (M : Matrix O I K) :
    (phaseWidthZero M).rank = ∑ o, (Finset.univ.filter (fun i ↦ M o i ≠ 0)).card := by
  rw [phaseWidthZero_eq_diagonal, Matrix.rank_diagonal, Fintype.card_subtype]
  simp only [Finset.card_filter, Fintype.sum_prod_type]

private def copyRegister (A : Type*) : Matrix (A × A) A K := fun p a ↦
  if p.1 = p.2 then (if p.1 = a then 1 else 0) else 0

/-- At zero height the flattening has the original matrix rank. -/
theorem rank_phaseHeightZero (M : Matrix O I K) : (phaseHeightZero M).rank = M.rank := by
  have hfactor : copyRegister O * M * (copyRegister I).transpose = phaseHeightZero M := by
    ext p q
    by_cases hp : p.1 = p.2 <;> by_cases hq : q.1 = q.2 <;>
      simp [copyRegister, hp, hq, phaseHeightZero, phaseEntry, Matrix.mul_apply, Matrix.transpose_apply,
        mul_ite, ite_mul]
  apply le_antisymm
  · rw [← hfactor]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  · have hsub : (phaseHeightZero M).submatrix (fun o ↦ (o, o)) (fun i ↦ (i, i)) = M := by
      ext o i
      simp [phaseHeightZero, phaseEntry, Matrix.submatrix]
    have hle := Matrix.rank_submatrix_le (phaseHeightZero M) (fun o ↦ (o, o)) (fun i ↦ (i, i))
    rwa [hsub] at hle

/-- Sharing one row label and one column label on their respective triangles
and applying the functional `M` at the common center gives the phase entries. -/
theorem phaseEntry_common_labels (M : Matrix O I K) (x : O) (y : I) (x' : O) (y' : I) :
    (∑ a : O, ∑ b : I, (if x = a then 1 else 0 : K) * (if x' = a then 1 else 0) *
      (if y = b then 1 else 0) * (if y' = b then 1 else 0) * M a b) = phaseEntry M x y x' y' := by
  by_cases hx : x = x' <;> by_cases hy : y = y' <;>
    simp [phaseEntry, hx, hy, ite_mul, mul_ite]

open MatrixMultiplication.Foundation

omit [Fintype I] in
/-- Grouping the two right sites yields a three-tensor with at most one
simple summand per row. This is the grouping `A,A',(B,B')` in the disk bound. -/
theorem rankAtMost_phase_group_right (M : Matrix O I K) :
    Tensor.RankAtMost (fun x x' (q : I × I) ↦ phaseEntry M x q.1 x' q.2) (Fintype.card O) := by
  let a (o x : O) : K := if x = o then 1 else 0
  let c (o : O) (q : I × I) : K := if q.1 = q.2 then M o q.1 else 0
  have heq : (fun x x' (q : I × I) ↦ phaseEntry M x q.1 x' q.2) =
      fun x x' q ↦ ∑ o, Tensor.rankOne (a o) (a o) (c o) x x' q := by
    funext x x' q
    by_cases h : x = x' <;> by_cases hq : q.1 = q.2 <;>
      simp [phaseEntry, a, c, Tensor.rankOne, h, hq, ite_mul, mul_ite]
  rw [heq]
  exact Tensor.rankAtMost_sum_rankOne a a c

omit [Fintype O] in
/-- Grouping the left sites gives the corresponding column bound. The order
`B',B,(A,A')` matches the second phase in the force argument. -/
theorem rankAtMost_phase_group_left (M : Matrix O I K) :
    Tensor.RankAtMost (fun y' y (p : O × O) ↦ phaseEntry M p.1 y p.2 y') (Fintype.card I) := by
  let a (i y : I) : K := if y = i then 1 else 0
  let c (i : I) (p : O × O) : K := if p.1 = p.2 then M p.1 i else 0
  have heq : (fun y' y (p : O × O) ↦ phaseEntry M p.1 y p.2 y') =
      fun y' y p ↦ ∑ i, Tensor.rankOne (a i) (a i) (c i) y' y p := by
    funext y' y p
    by_cases h : y' = y <;> by_cases hp : p.1 = p.2 <;>
      simp [phaseEntry, a, c, Tensor.rankOne, h, hp, ite_mul, mul_ite, Ne.symm]
  rw [heq]
  exact Tensor.rankAtMost_sum_rankOne a a c

end

end

end FiniteFourier
end LinearAlgebra
end OAI

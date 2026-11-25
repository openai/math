import OAI.Optimization.LinearProgramming.Elimination.Solve
import OAI.Optimization.LinearProgramming.Recovery.Presentation

/-! A finite-matrix bridge from a presentation `B(ker A)` to the independent complementary
row bases used by the geometric label test. All basis columns are computed by linear solves.
The construction applies to arbitrary ordered fields, including rank-zero matrices. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery

open Matrix Submodule Module
open scoped Matrix

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {m n k : ℕ}

/-- Over an ordered field the column spaces of `A Aᵀ` and `A` coincide. -/
theorem gram_range (A : Matrix (Fin m) (Fin n) K) :
    LinearMap.range (A * Aᵀ).mulVecLin = LinearMap.range A.mulVecLin := by
  apply Submodule.eq_of_le_of_finrank_le
  · rintro x ⟨v,rfl⟩
    refine ⟨Aᵀ *ᵥ v, ?_⟩
    change A *ᵥ (Aᵀ *ᵥ v) = (A*Aᵀ) *ᵥ v
    exact Matrix.mulVec_mulVec v A Aᵀ
  · exact (Matrix.rank_self_mul_transpose A).ge

/-- Solve `A Aᵀ u_j=A_j` once for each input column, with one materialized Gram matrix. -/
def gramSolutions (A : Matrix (Fin m) (Fin n) K) : Matrix (Fin m) (Fin n) K :=
  let G := Elimination.tabulate (A*Aᵀ)
  let v := Vector.ofFn fun j : Fin n => (Elimination.solve G (A.col j)).getD 0
  Matrix.of fun i j => v[j] i

theorem gramSolutions_spec (A : Matrix (Fin m) (Fin n) K) : (A*Aᵀ) * gramSolutions A = A := by
  ext i j
  have hcol : A.col j ∈ LinearMap.range (A*Aᵀ).mulVecLin := by
    rw [gram_range, Matrix.range_mulVecLin]
    exact Submodule.subset_span ⟨j,rfl⟩
  obtain ⟨z,hz⟩ := Elimination.solve_complete (A*Aᵀ) (A.col j) hcol
  have hv := congrFun (Elimination.solve_sound _ _ _ hz) i
  simpa [gramSolutions, Elimination.tabulate_eq, hz, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.col_apply]
    using hv

/-- The columns of this matrix span precisely the homogeneous solutions of `A`. -/
def kernelMatrix (A : Matrix (Fin m) (Fin n) K) : Matrix (Fin n) (Fin n) K :=
  Elimination.tabulate (1 - Aᵀ * gramSolutions A)

theorem kernelMatrix_range (A : Matrix (Fin m) (Fin n) K) :
    LinearMap.range (kernelMatrix A).mulVecLin = LinearMap.ker A.mulVecLin := by
  let P := kernelMatrix A
  have hp : P = 1 - Aᵀ * gramSolutions A := Elimination.tabulate_eq _
  have left : A * P = 0 := by rw [hp, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, gramSolutions_spec, sub_self]
  have right : LinearMap.ker A.mulVecLin ≤ LinearMap.range Pᵀ.mulVecLin := by
    intro x hx
    change A *ᵥ x = 0 at hx
    refine ⟨x,?_⟩
    change Pᵀ *ᵥ x = x
    rw [hp, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
      hx, Matrix.mulVec_zero, sub_zero]
  apply Submodule.eq_of_le_of_finrank_le
  · rintro x ⟨v,rfl⟩
    change A *ᵥ (P *ᵥ v) = 0
    rw [Matrix.mulVec_mulVec, left, Matrix.zero_mulVec]
  · have h := Submodule.finrank_mono right
    change Module.finrank K (LinearMap.ker A.mulVecLin) ≤ Pᵀ.rank at h
    rwa [Matrix.rank_transpose] at h

namespace Presentation

/-- One explicit matrix whose column space is the space described by the presentation. -/
def generatorMatrix (u : Presentation K n) : Matrix (Fin n) (Fin u.nVars) K :=
  u.output * kernelMatrix u.equations

theorem generatorMatrix_range (u : Presentation K n) :
    LinearMap.range u.generatorMatrix.mulVecLin = u.denote := by
  rw [generatorMatrix,Matrix.mulVecLin_mul,LinearMap.range_comp,kernelMatrix_range,denote]

/-- Use actual input column indices chosen by the verified Gram-determinant scan. -/
def basisRows (G : Matrix (Fin n) (Fin k) K) : Matrix (Fin (Elimination.columnBasis G).length) (Fin n) K :=
  (Elimination.columns G (Elimination.columnBasis G))ᵀ

theorem basisRows_independent (G : Matrix (Fin n) (Fin k) K) : LinearIndependent K (basisRows G).row :=
  (Elimination.columnBasis_spec G).1

theorem basisRows_span (G : Matrix (Fin n) (Fin k) K) :
    Submodule.span K (Set.range (basisRows G).row) = LinearMap.range G.mulVecLin := by
  rw [Matrix.range_mulVecLin]
  exact (Elimination.columnBasis_spec G).2

/-- Columns complementary to `generatorMatrix`, obtained from its transpose equations. -/
def dualGeneratorMatrix (u : Presentation K n) : Matrix (Fin n) (Fin n) K :=
  kernelMatrix u.generatorMatrixᵀ

/-- The dimensions, both basis-independence properties, orthogonality and exact primal row span
needed to instantiate the geometry. In particular the entire row count is the input's ambient `n`. -/
theorem complementary_basis_spec (u : Presentation K n) :
    let G := u.generatorMatrix
    let H := u.dualGeneratorMatrix
    LinearIndependent K (basisRows G).row ∧ LinearIndependent K (basisRows H).row ∧
    basisRows G * (basisRows H)ᵀ = 0 ∧
    (Elimination.columnBasis G).length + (Elimination.columnBasis H).length = n ∧
    Submodule.span K (Set.range (basisRows G).row) = u.denote := by
  let G := u.generatorMatrix
  let H := u.dualGeneratorMatrix
  have hH : LinearMap.range H.mulVecLin = LinearMap.ker Gᵀ.mulVecLin := kernelMatrix_range _
  refine ⟨basisRows_independent _,basisRows_independent _,?_,?_,(basisRows_span G).trans u.generatorMatrix_range⟩
  · ext i j
    change (basisRows G i) ⬝ᵥ (basisRows H j) = 0
    have hi : basisRows G i ∈ LinearMap.range G.mulVecLin := by
      rw [← basisRows_span]; exact Submodule.subset_span ⟨i,rfl⟩
    have hj : basisRows H j ∈ LinearMap.ker Gᵀ.mulVecLin := by
      rw [← hH,← basisRows_span]; exact Submodule.subset_span ⟨j,rfl⟩
    rw [← denote_kernel,transpose_kernel,denote_columns] at hj
    exact hj _ hi
  · rw [Elimination.columnBasis_length,Elimination.columnBasis_length]
    have rank_nullity := Gᵀ.mulVecLin.finrank_range_add_finrank_ker
    rw [← hH] at rank_nullity
    change Gᵀ.rank + H.rank = _ at rank_nullity
    simpa only [Matrix.rank_transpose,Module.finrank_pi,Fintype.card_fin] using rank_nullity

end Presentation
end Recovery
end LinearProgramming
end Optimization
end OAI

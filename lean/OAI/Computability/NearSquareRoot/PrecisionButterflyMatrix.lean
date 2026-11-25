import OAI.Computability.NearSquareRoot.PrecisionButterflyLayer
import OAI.Computability.NearSquareRoot.SynchronizedNorm

/-! # Matrix specification of the two-point Walsh tape pass -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedPoint

open Matrix Kronecker
noncomputable section

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

/-- For a low address bit the full layer is the identity on every spectator
coordinate tensored with the two-point Walsh matrix. -/
def butterflyMatrix : Matrix (ι × Bool) (ι × Bool) ℂ :=
  (1 : Matrix ι ι ℂ) ⊗ₖ SynchronizedPair.walsh.submatrix finTwoEquiv.symm finTwoEquiv.symm

private theorem walsh_selfAdjoint : SynchronizedPair.walshᴴ = SynchronizedPair.walsh := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [SynchronizedPair.walsh, conjTranspose_apply]

theorem butterflyMatrix_unitary : (butterflyMatrix ι)ᴴ * butterflyMatrix ι = 1 := by
  rw [butterflyMatrix, conjTranspose_kronecker, conjTranspose_one, conjTranspose_submatrix,
    ← mul_kronecker_mul, one_mul, walsh_selfAdjoint, submatrix_mul_equiv,
    SynchronizedPair.walsh_sq, submatrix_one_equiv, one_kronecker_one]

theorem butterflyMatrix_apply (x : ι × Bool → ℂ) (i : ι) (b : Bool) :
    (butterflyMatrix ι *ᵥ x) (i,b) =
      (SynchronizedPair.w : ℂ) * butterflySum b (x (i,false)) (x (i,true)) := by
  simp only [butterflyMatrix, mulVec, dotProduct, Fintype.sum_prod_type,
    kroneckerMap_apply, Matrix.one_apply, Matrix.submatrix_apply, ite_mul, one_mul, zero_mul]
  simp only [Fintype.sum_bool]
  cases b <;> simp [SynchronizedPair.walsh, finTwoEquiv, butterflySum, Finset.sum_add_distrib] <;> ring

theorem directWalsh_eq_matrix (x : EuclideanSpace ℂ (ι × Bool)) :
    directWalsh ι x = SynchronizedPadding.matrixIsometry _ (butterflyMatrix_unitary ι) x := by
  ext ⟨i,b⟩
  exact (butterflyMatrix_apply ι x i b).symm

/-- Local input/output guarantee in the matrix schedule's representation. -/
theorem record_butterfly_error {k : ℕ} (hk : 1 ≤ k) (hcard : Fintype.card (ι × Bool) ≤ 2^k)
    (x : ι × Bool → Record k) (hx : ‖recordArray x‖ ≤ (2 : ℝ)^(13*k)) :
    ‖recordArray (fun j : ι × Bool =>
        normalizedBranch k j.2 (x (j.1,false)) (x (j.1,true)) (butterflyCoefficient k)) -
      SynchronizedPadding.matrixIsometry _ (butterflyMatrix_unitary ι) (recordArray x)‖ ≤
      1 / (2 : ℝ)^(50*k) := by
  rw [← directWalsh_eq_matrix]
  exact directWalsh_record_error ι hk hcard x hx

end
end FixedPoint

end NearSquareRoot
end Computability
end OAI

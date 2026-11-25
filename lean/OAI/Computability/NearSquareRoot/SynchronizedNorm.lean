import OAI.Computability.NearSquareRoot.SynchronizedLayerTensor
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Euclidean norm preservation for the full padded product transform. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace SynchronizedPadding

open Matrix Finset WithLp

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The matrix of the exact pass, acting on the Euclidean array space. -/
noncomputable def matrixIsometry (M : Matrix I I ℂ) (hM : Mᴴ * M = 1) :
    EuclideanSpace ℂ I ≃ₗᵢ[ℂ] EuclideanSpace ℂ I :=
  Unitary.linearIsometryEquiv <|
    ⟨Matrix.toEuclideanCLM (𝕜 := ℂ) (n := I) M,
      Unitary.map_mem (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := I)) (Matrix.mem_unitaryGroup_iff'.2 hM)⟩

@[simp] theorem matrixIsometry_apply (M : Matrix I I ℂ) (hM : Mᴴ * M = 1) (x : I → ℂ) :
    matrixIsometry M hM (toLp 2 x) = toLp 2 (M *ᵥ x) := rfl

@[simp] theorem matrixIsometry_symm_apply (M : Matrix I I ℂ) (hM : Mᴴ * M = 1) (x : I → ℂ) :
    (matrixIsometry M hM).symm (toLp 2 x) = toLp 2 (Mᴴ *ᵥ x) := by
  change star (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := I) M) (toLp 2 x) = _
  rw [← map_star]
  rfl

section Tensor

variable {ι : Type*} {A B : ι → Type*} [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]

theorem tensorMatrix_unitary (U : ∀ i, Matrix (A i) (A i) ℂ) (h : ∀ i, (U i)ᴴ * U i = 1) :
    (tensorMatrix U)ᴴ * tensorMatrix U = 1 := by
  simp only [tensorMatrix_conjTranspose, ← tensorMatrix_mul, h, tensorMatrix_one]

variable [∀ i, Fintype (B i)] [∀ i, DecidableEq (B i)]

/-- A padded product of unitary axis matrices is itself unitary on the full box,
including inputs supported on unused cells. -/
theorem tensorMatrix_axisPadding_unitary (U : ∀ i, Matrix (A i) (A i) ℂ) (h : ∀ i, (U i)ᴴ * U i = 1) :
    let P := tensorMatrix (fun i ↦ axisPadding (b := B i) (U i))
    Pᴴ * P = 1 := by
  apply tensorMatrix_unitary
  intro i
  simp [axisPadding, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_one, h]

end Tensor

end SynchronizedPadding

end NearSquareRoot
end Computability
end OAI

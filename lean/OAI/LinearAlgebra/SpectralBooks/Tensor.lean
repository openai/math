import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorFlattening
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Rectangular matrix multiplication over a field

We use the finite coefficient tensors and Kronecker powers from the matrix
multiplication library. The dimensions are the shared wire sizes, in the
paper's order `12, 23, 31`. The first site's coordinates are consequently
indexed by `Fin n31 × Fin n12`.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section

open MatrixMultiplication.Foundation
open scoped BigOperators

section

section Rank

variable {F X Y Z : Type*} [Field F] [Fintype X] [Fintype Y]

/-- Expanding in the coordinate bases of the first two sites gives a finite
decomposition into simple tensors. -/
theorem exists_rankAtMost (T : Tensor F X Y Z) : ∃ r, Tensor.RankAtMost T r := by
  classical
  let a : X × Y → X → F := fun p x => if p.1 = x then 1 else 0
  let b : X × Y → Y → F := fun p y => if p.2 = y then 1 else 0
  let c : X × Y → Z → F := fun p => T p.1 p.2
  refine ⟨Fintype.card (X × Y), ?_⟩
  have h : T = fun x y z => ∑ p, Tensor.rankOne (a p) (b p) (c p) x y z := by
    funext x y z
    simp [a, b, c, Tensor.rankOne, Fintype.sum_prod_type, ite_mul, mul_ite]
  rw [h]
  exact Tensor.rankAtMost_sum_rankOne a b c

/-- The least number of simple tensors in a decomposition over the ground field. -/
def tensorRank (T : Tensor F X Y Z) : ℕ := by
  classical
  exact Nat.find (exists_rankAtMost T)

theorem rankAtMost_tensorRank (T : Tensor F X Y Z) : Tensor.RankAtMost T (tensorRank T) := by
  classical
  exact Nat.find_spec (exists_rankAtMost T)

theorem tensorRank_le_of_rankAtMost {T : Tensor F X Y Z} {r : ℕ}
    (h : Tensor.RankAtMost T r) : tensorRank T ≤ r := by
  classical
  exact Nat.find_min' (exists_rankAtMost T) h

/-- The infimum of the positive tensor-power rank roots. -/
def asymptoticRank (T : Tensor F X Y Z) : ℝ :=
  ⨅ n : ℕ, (tensorRank (Tensor.power T (n + 1)) : ℝ) ^ ((n + 1 : ℝ)⁻¹)

theorem asymptoticRank_nonneg (T : Tensor F X Y Z) : 0 ≤ asymptoticRank T :=
  le_ciInf (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem asymptoticRank_le_tensorRank (T : Tensor F X Y Z) :
    asymptoticRank T ≤ tensorRank T := by
  have hu := ciInf_le ⟨(0 : ℝ), by rintro _ ⟨n, rfl⟩; positivity⟩ (0 : ℕ)
    (f := fun n : ℕ => (tensorRank (Tensor.power T (n + 1)) : ℝ) ^ ((n + 1 : ℝ)⁻¹))
  have h₁ := tensorRank_le_of_rankAtMost ((rankAtMost_tensorRank T).power 1)
  simp only [pow_one] at h₁
  apply le_trans _ (Nat.cast_le (α := ℝ) |>.mpr h₁)
  simpa [asymptoticRank] using hu

end Rank

/-- The coefficient of the cyclic pattern `e_{ki} ⊗ e_{ij} ⊗ e_{jk}` is one. -/
abbrev matrixTensor (F : Type*) [Field F] (n12 n23 n31 : ℕ) :=
  Tensor.matrixCoefficients (K := F) (Fin n31) (Fin n12) (Fin n23)

end

end

end SpectralBooks
end LinearAlgebra
end OAI

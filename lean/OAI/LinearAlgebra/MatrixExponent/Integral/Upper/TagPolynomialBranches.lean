import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.Coefficients
import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.TagHeterogeneous
import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.PolynomialFiltration
import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.Character.Permutations
import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.Character.PolynomialValues

open OAI.LinearAlgebra.MatrixExponent.Integral OAI.LinearAlgebra.TensorSpectrum

/-!
# Polynomial branches in the heterogeneous tag construction

The determinant branches retain their actual output coordinates; finite
coordinate equivalences identify their classes with polynomial multiplication.
The middle tripling branch is a last-two-leg swap followed by the stated
invertible reversal of the shared first coordinate.
-/

noncomputable section

open OAI.MatrixMultiplication.Foundation

namespace OAI.LinearAlgebra.MatrixExponent.Integral.Upper.TagHeterogeneous

/-- The larger retained branch of the determinant filtration. -/
def determinantQuotientTensor (a b : ℕ) :
    Tensor O (Fin (a + 1)) (Fin (b + 3)) (Fin (a + b + 3)) :=
  fun i j k => if i.val + j.val = k.val then 1 else 0

/-- The smaller retained branch of the determinant filtration. -/
def determinantKernelTensor (a b : ℕ) :
    Tensor O (Fin (a + 1)) (Fin (b + 1)) (Fin (a + b + 1)) :=
  fun i j k => if i.val + j.val = k.val then 1 else 0

theorem determinantGradedTensor_eq_sharedTwo (a b : ℕ) :
    determinantGradedTensor a b =
      sharedTwo (determinantQuotientTensor a b) (determinantKernelTensor a b) := by
  funext i j k
  cases j <;> cases k <;> rfl

theorem ofTensor_determinantQuotient (a b : ℕ) :
    TensorClass.ofTensor (determinantQuotientTensor a b) =
      TensorClass.ofTensor (polynomialTensor (a + 1) (b + 3)) := by
  let e : Fin (a + b + 3) ≃ Fin (a + 1 + (b + 3) - 1) := finCongr (by omega)
  have heq : determinantQuotientTensor a b =
      Tensor.pullback (Equiv.refl _) (Equiv.refl _) e
        (polynomialTensor (a + 1) (b + 3)) := by
    funext i j k
    rfl
  rw [heq]
  exact TensorClass.ofTensor_pullback_equiv _ _ _ _

theorem ofTensor_determinantKernel (a b : ℕ) :
    TensorClass.ofTensor (determinantKernelTensor a b) =
      TensorClass.ofTensor (polynomialTensor (a + 1) (b + 1)) := by
  let e : Fin (a + b + 1) ≃ Fin (a + 1 + (b + 1) - 1) := finCongr (by omega)
  have heq : determinantKernelTensor a b =
      Tensor.pullback (Equiv.refl _) (Equiv.refl _) e
        (polynomialTensor (a + 1) (b + 1)) := by
    funext i j k
    rfl
  rw [heq]
  exact TensorClass.ofTensor_pullback_equiv _ _ _ _

/-- The uniform separation input is the whole graded determinant tensor. -/
theorem ofTensor_determinant_uniform (a b : ℕ) :
    TensorClass.ofTensor (Separation.shared
      (twoFamily (determinantQuotientTensor a b) (determinantKernelTensor a b))) =
      TensorClass.ofTensor (determinantGradedTensor a b) := by
  rw [ofTensor_shared_twoFamily, determinantGradedTensor_eq_sharedTwo]

/-- Both original polynomial branches survive zero padding exactly. -/
theorem ofTensor_determinant_family (a b : ℕ) (j : Fin 2) :
    TensorClass.ofTensor
      (twoFamily (determinantQuotientTensor a b) (determinantKernelTensor a b) j) =
      ![TensorClass.ofTensor (polynomialTensor (a + 1) (b + 3)),
        TensorClass.ofTensor (polynomialTensor (a + 1) (b + 1))] j := by
  rw [ofTensor_twoFamily, ofTensor_determinantQuotient, ofTensor_determinantKernel]

/-- This reversal is an actual equivalence, including the empty finite type. -/
def triplingReverseEquiv (a : ℕ) : Fin a ≃ Fin a where
  toFun := triplingReverse
  invFun := triplingReverse
  left_inv := triplingReverse_involutive
  right_inv := triplingReverse_involutive

/-- The middle branch is evaluated using the permuted character. Its
first-coordinate reversal is removed only by an invertible local map. -/
theorem ofTensor_triplingMiddle (a h : ℕ) :
    TensorClass.ofTensor (triplingMiddleTensor a h) =
      TensorClass.swapYZ (TensorClass.ofTensor (polynomialTensor a h)) := by
  have heq : triplingMiddleTensor a h =
      Tensor.pullback (triplingReverseEquiv a) (Equiv.refl _) (Equiv.refl _)
        (CoefficientTensor.swapYZ (polynomialTensor a h)) := rfl
  rw [heq, TensorClass.ofTensor_pullback_equiv, TensorClass.swapYZ_ofTensor]

theorem ofTensor_tripling_family (a h : ℕ) (j : Fin 3) :
    TensorClass.ofTensor
      (threeFamily (polynomialTensor a h) (triplingMiddleTensor a h)
        (polynomialTensor a h) j) =
      ![TensorClass.ofTensor (polynomialTensor a h),
        TensorClass.swapYZ (TensorClass.ofTensor (polynomialTensor a h)),
        TensorClass.ofTensor (polynomialTensor a h)] j := by
  rw [ofTensor_threeFamily, ofTensor_triplingMiddle]

/-- Positivity for every padded determinant branch follows from the already
established positive polynomial character values. -/
theorem determinant_family_value_pos (f : TensorClass.Character) (a b : ℕ) (j : Fin 2) :
    0 < (f (TensorClass.ofTensor
      (twoFamily (determinantQuotientTensor a b) (determinantKernelTensor a b) j)) : ℝ) := by
  rw [ofTensor_determinant_family]
  fin_cases j <;> simp only
  · exact f.polynomial_value_pos _ _ (by omega) (by omega)
  · exact f.polynomial_value_pos _ _ (by omega) (by omega)

/-- The positive middle value uses the actual permuted character. -/
theorem tripling_middle_value_pos (f : TensorClass.Character) (a h : ℕ)
    (ha : 1 ≤ a) (hh : 1 ≤ h) :
    0 < (f (TensorClass.ofTensor (triplingMiddleTensor a h)) : ℝ) := by
  rw [ofTensor_triplingMiddle]
  have hp := (f.permuted 2).polynomial_value_pos a h ha hh
  simpa [TensorClass.Character.permuted_apply, TensorClass.permute,
    TensorClass.permuteHom, TensorClass.swapYZHom] using hp

/-- These strict positive values are the hypotheses of the uniform tag
inequality, including the padded and reversed middle branch. -/
theorem tripling_family_value_pos (f : TensorClass.Character) (a h : ℕ)
    (ha : 1 ≤ a) (hh : 1 ≤ h) (j : Fin 3) :
    0 < (f (TensorClass.ofTensor
      (threeFamily (polynomialTensor a h) (triplingMiddleTensor a h)
        (polynomialTensor a h) j)) : ℝ) := by
  rw [ofTensor_threeFamily]
  fin_cases j <;> simp only
  · exact f.polynomial_value_pos _ _ ha hh
  · exact tripling_middle_value_pos f a h ha hh
  · exact f.polynomial_value_pos _ _ ha hh

end OAI.LinearAlgebra.MatrixExponent.Integral.Upper.TagHeterogeneous

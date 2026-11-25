import OAI.LinearAlgebra.MatrixExponent.Coefficients
import OAI.LinearAlgebra.MatrixExponent.Upper.Character.Degeneration
import OAI.LinearAlgebra.MatrixExponent.Upper.Character.DotsPower
import OAI.LinearAlgebra.MatrixExponent.Upper.PolynomialFiltrationFamily
import OAI.LinearAlgebra.MatrixExponent.Upper.PolynomialSectorFamily

open OAI.LinearAlgebra.MatrixExponent OAI.LinearAlgebra.TensorSpectrum

/-!
# Character bounds from the two explicit polynomial families

Both inequalities use the actual finite-degree restriction witnesses.  In
the determinant case the two-dimensional pairing is explicitly charged.
-/

noncomputable section

open OAI.MatrixMultiplication.Foundation

namespace OAI.LinearAlgebra.MatrixExponent.Upper.TensorClass

theorem binaryDotTensor_class : ofTensor binaryDotTensor = dotX 2 := by
  have heq : Tensor.pullback (Equiv.refl Unit) finTwoEquiv finTwoEquiv
      binaryDotTensor = CoefficientTensor.dotXCoeff 2 := by
    funext x y z
    simp [Tensor.pullback, binaryDotTensor, CoefficientTensor.dotXCoeff]
  change ofTensor binaryDotTensor = ofTensor (CoefficientTensor.dotXCoeff 2)
  rw [← heq]
  exact (ofTensor_pullback_equiv _ _ _ _).symm

theorem Character.determinant_graded_le (f : Character) (a b : ℕ) :
    (f (ofTensor (determinantGradedTensor a b)) : ℝ) ≤
      (2 : ℝ) ^ f.pX * (f (ofTensor (polynomialTensor (a + 1) (b + 2))) : ℝ) := by
  have h := f.polynomial_constant_le
    (Tensor.product (polynomialTensor (a + 1) (b + 2)) binaryDotTensor)
    (determinantGradedTensor a b) (determinantPolynomialFamily a b) 1
    (fun i y z => congrFun (congrFun (congrFun
      (determinantPolynomialFamily_coeff_zero a b) i) y) z)
    (determinantPolynomialFamily_degree_le a b)
    (fun t ht => determinantPolynomialFamily_eval_mem_restrictionOrbit a b ht)
  rw [← ofTensor_mul, Character.map_mul, binaryDotTensor_class] at h
  have hr : (f (ofTensor (determinantGradedTensor a b)) : ℝ) ≤
      (f (ofTensor (polynomialTensor (a + 1) (b + 2))) : ℝ) * f.dotXValue 2 := by
    exact_mod_cast h
  rw [f.dotXValue_eq_rpow 2 (by decide), mul_comm] at hr
  exact hr

theorem Character.tripling_graded_le (f : Character) (a h : ℕ)
    (ha : 1 ≤ a) (hh : 1 ≤ h) :
    (f (ofTensor (triplingSectorTensor a h)) : ℝ) ≤
      (f (ofTensor (polynomialTensor a (3 * h + a - 1))) : ℝ) := by
  have hbound := f.polynomial_constant_le
    (polynomialTensor a (triplingWidth a h)) (triplingSectorTensor a h)
    (triplingPolynomialFamily a h ha hh) 1
    (triplingPolynomialFamily_coeff_zero a h ha hh)
    (triplingPolynomialFamily_degree_le a h ha hh)
    (fun t ht => triplingPolynomialFamily_eval_mem_restrictionOrbit a h ha hh ht)
  exact_mod_cast hbound

end OAI.LinearAlgebra.MatrixExponent.Upper.TensorClass

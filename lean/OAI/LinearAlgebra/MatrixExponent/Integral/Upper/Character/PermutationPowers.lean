import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.Coefficients
import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.Character.Permutations
import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.Character.DotsPower

open OAI.LinearAlgebra.MatrixExponent.Integral OAI.LinearAlgebra.TensorSpectrum

/-!
# The exponents of the six permuted characters

The exponent identities below follow from evaluating the actual pairings at
dimension two. In particular, they do not depend on how the power-law witnesses
were chosen. Polynomial multiplication with one scalar input is identified
with the corresponding actual pairing by explicit coordinate equivalences.
-/

noncomputable section

open scoped BigOperators
open OAI.MatrixMultiplication.Foundation

namespace OAI.LinearAlgebra.MatrixExponent.Integral.Upper.TensorClass

/-- Scalar polynomial input and full output give the first-leg pairing,
including the empty second input case. -/
theorem polynomialTensor_one_left_class (n : ℕ) :
    ofTensor (polynomialTensor 1 n) = dotX n := by
  let u : Fin 1 ≃ Unit := Equiv.ofUnique _ _
  let e : Fin (1 + n - 1) ≃ Fin n := finCongr (by omega)
  have h : polynomialTensor 1 n =
      Tensor.pullback u (Equiv.refl _) e (CoefficientTensor.dotXCoeff n) := by
    funext i j k
    simp [Tensor.pullback, CoefficientTensor.dotXCoeff,
      Fin.ext_iff, e]
  change ofTensor (polynomialTensor 1 n) = ofTensor (CoefficientTensor.dotXCoeff n)
  rw [h]
  exact ofTensor_pullback_equiv _ _ _ _

namespace Character

private theorem rpow_two_injective {p q : ℝ}
    (h : (2 : ℝ) ^ p = (2 : ℝ) ^ q) : p = q := by
  have hlog := congrArg Real.log h
  rw [Real.log_rpow (by norm_num), Real.log_rpow (by norm_num)] at hlog
  have hpos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  nlinarith

theorem permuted_dotXValue (f : Character) (i : Fin 6) (n : ℕ) :
    (f.permuted i).dotXValue n =
      ![f.dotXValue n, f.dotYValue n, f.dotXValue n,
        f.dotYValue n, f.dotZValue n, f.dotZValue n] i := by
  unfold dotXValue
  rw [f.permuted_dotX]
  fin_cases i <;> rfl

/-- The first-leg exponents of the six actual characters, with their
multiplicities. Uniqueness is forced by the value at dimension two. -/
theorem permuted_pX (f : Character) (i : Fin 6) :
    (f.permuted i).pX = ![f.pX, f.pY, f.pX, f.pY, f.pZ, f.pZ] i := by
  apply rpow_two_injective
  have hvalue := (f.permuted i).dotXValue_eq_rpow 2 (by norm_num)
  simp only [Nat.cast_ofNat] at hvalue
  rw [← hvalue, permuted_dotXValue]
  simp only [f.dotXValue_eq_rpow 2 (by norm_num),
    f.dotYValue_eq_rpow 2 (by norm_num), f.dotZValue_eq_rpow 2 (by norm_num),
    Nat.cast_ofNat]
  fin_cases i <;> rfl

theorem sum_permuted_pX (f : Character) :
    (∑ i : Fin 6, (f.permuted i).pX) = 2 * (f.pX + f.pY + f.pZ) := by
  simp [permuted_pX, Fin.sum_univ_succ]
  ring

/-- The average of the character's three pairing exponents. -/
def meanExponent (f : Character) : ℝ := (f.pX + f.pY + f.pZ) / 3

theorem meanExponent_nonneg (f : Character) : 0 ≤ f.meanExponent :=
  div_nonneg f.sum_exponents_nonneg (by norm_num)

theorem meanExponent_le_one (f : Character) : f.meanExponent ≤ 1 := by
  unfold meanExponent
  linarith [f.sum_exponents_le_three]

theorem sum_exponents_eq_three_meanExponent (f : Character) :
    f.pX + f.pY + f.pZ = 3 * f.meanExponent := by
  unfold meanExponent
  ring

theorem sum_permuted_pX_eq_six_meanExponent (f : Character) :
    (∑ i : Fin 6, (f.permuted i).pX) = 6 * f.meanExponent := by
  rw [sum_permuted_pX]
  unfold meanExponent
  ring

/-- A permutation cannot change the sum of the three exponents, since it
preserves the square matrix multiplication tensor at every dimension. -/
theorem sum_exponents_permuted (f : Character) (i : Fin 6) :
    (f.permuted i).pX + (f.permuted i).pY + (f.permuted i).pZ =
      f.pX + f.pY + f.pZ := by
  apply rpow_two_injective
  have hleft := (f.permuted i).square_value_eq_rpow 2 (by norm_num)
  have hright := f.square_value_eq_rpow 2 (by norm_num)
  simp only [Nat.cast_ofNat] at hleft hright
  rw [← hleft, ← hright, f.permuted_square]

@[simp] theorem meanExponent_permuted (f : Character) (i : Fin 6) :
    (f.permuted i).meanExponent = f.meanExponent := by
  unfold meanExponent
  rw [sum_exponents_permuted]

theorem permuted_polynomialTensor_one_left_value
    (f : Character) (i : Fin 6) (n : ℕ) (hn : 1 ≤ n) :
    (f.permuted i (ofTensor (polynomialTensor 1 n)) : ℝ) =
      (n : ℝ) ^ (f.permuted i).pX := by
  rw [polynomialTensor_one_left_class]
  exact (f.permuted i).dotXValue_eq_rpow n hn

/-- The six boundary values are the powers with exponents
`pX, pY, pX, pY, pZ, pZ`. -/
theorem permuted_polynomialTensor_one_left_vector
    (f : Character) (i : Fin 6) (n : ℕ) (hn : 1 ≤ n) :
    (f.permuted i (ofTensor (polynomialTensor 1 n)) : ℝ) =
      (n : ℝ) ^ (![f.pX, f.pY, f.pX, f.pY, f.pZ, f.pZ] i) := by
  rw [permuted_polynomialTensor_one_left_value f i n hn, permuted_pX]

theorem permuted_polynomialTensor_one_right_value
    (f : Character) (i : Fin 6) (n : ℕ) (hn : 1 ≤ n) :
    (f.permuted i (ofTensor (polynomialTensor n 1)) : ℝ) =
      (n : ℝ) ^ (f.permuted (permuteSwapXY i)).pX := by
  rw [← swapXY_polynomialTensor 1 n, f.permuted_swapXY]
  exact f.permuted_polynomialTensor_one_left_value (permuteSwapXY i) n hn

end Character
end OAI.LinearAlgebra.MatrixExponent.Integral.Upper.TensorClass

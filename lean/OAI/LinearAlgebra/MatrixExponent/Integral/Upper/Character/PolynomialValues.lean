import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.Coefficients
import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.Character.TagFinite
import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.PolynomialTensor

open OAI.LinearAlgebra.MatrixExponent.Integral OAI.LinearAlgebra.TensorSpectrum

noncomputable section

/-!
# Positivity and rank bounds for polynomial character values

The constant input monomials witness nonvanishing.  The upper bound uses the
actual evaluation/interpolation rank decomposition of ordinary convolution.
-/

open OAI.MatrixMultiplication.Foundation

namespace OAI.LinearAlgebra.MatrixExponent.Integral.Upper

theorem polynomialTensor_ne_zero {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    polynomialTensor a b ≠ 0 := by
  intro heq
  let i : Fin a := ⟨0, by omega⟩
  let j : Fin b := ⟨0, by omega⟩
  let k : Fin (a + b - 1) := ⟨0, by omega⟩
  have h := congrFun (congrFun (congrFun heq i) j) k
  norm_num [polynomialTensor, i, j, k] at h

namespace TensorClass

theorem Character.polynomial_value_pos (f : Character) (a b : ℕ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) :
    0 < (f (ofTensor (polynomialTensor a b)) : ℝ) := by
  have h := f.one_le_of_tensor_unit (polynomialTensor a b)
    ⟨⟨0, by omega⟩, ⟨0, by omega⟩, ⟨0, by omega⟩, by simp [polynomialTensor]⟩
  have hr : (1 : ℝ) ≤ f (ofTensor (polynomialTensor a b)) := by exact_mod_cast h
  linarith

theorem Character.polynomial_value_le (f : Character) (a b : ℕ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (f (ofTensor (polynomialTensor a b)) : ℝ) ≤ (a : ℝ) + (b : ℝ) - 1 := by
  have hRank : rank (ofTensor (polynomialTensor a b)) ≤ a + b - 1 := by
    rw [rank_ofTensor]
    exact (CoefficientTensor.rank_le_iff _ _).mpr (polynomialTensor_rankAtMost a b)
  have hnn : f (ofTensor (polynomialTensor a b)) ≤ (a + b - 1 : ℕ) :=
    (f.le_rank _).trans (Nat.cast_le.mpr hRank)
  have hr : (f (ofTensor (polynomialTensor a b)) : ℝ) ≤ ((a + b - 1 : ℕ) : ℝ) := by
    exact_mod_cast hnn
  have hab : 1 ≤ a + b := by omega
  simpa only [Nat.cast_sub hab, Nat.cast_add, Nat.cast_one] using hr

end TensorClass
end OAI.LinearAlgebra.MatrixExponent.Integral.Upper

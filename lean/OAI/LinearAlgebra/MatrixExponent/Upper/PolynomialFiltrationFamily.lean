import OAI.LinearAlgebra.MatrixExponent.Coefficients
import OAI.LinearAlgebra.MatrixExponent.Upper.PolynomialFiltration
import OAI.LinearAlgebra.MatrixExponent.Upper.PolynomialWeightFamily

open OAI.LinearAlgebra.MatrixExponent OAI.LinearAlgebra.TensorSpectrum

/-!
# The finite-degree determinant family

The constant coefficient is the two-branch graded tensor.  Every nonzero
evaluation is an actual restriction of the original convolution tensor times
the two-dimensional pairing.  These explicit data, rather than continuity of
an arbitrary tensor character, are the inputs to finite interpolation.
-/

noncomputable section
open OAI.MatrixMultiplication.Foundation

namespace OAI.LinearAlgebra.MatrixExponent.Upper

theorem determinantAdapted_mem_restrictionOrbit (a b : ℕ) :
    determinantAdaptedTensor a b ∈ LocalTensor.orbit
      (Tensor.product (polynomialTensor (a + 1) (b + 2)) binaryDotTensor) := by
  have hd : doubledPolynomialTensor a b ∈ LocalTensor.orbit
      (Tensor.product (polynomialTensor (a + 1) (b + 2)) binaryDotTensor) := by
    rw [← doubledPolynomialTensor_product, Tensor.pullback_eq_restrict]
    exact ⟨_, _, _, rfl⟩
  have h := LocalTensor.restrict_mem hd
    (fun i' i : Fin (a + 1) => if i = i' then (1 : Coeff) else 0)
    (determinantInputMap b) (determinantOutputMap a b)
  have he : Tensor.restrict
      (fun i' i : Fin (a + 1) => if i = i' then (1 : Coeff) else 0)
      (determinantInputMap b) (determinantOutputMap a b)
      (doubledPolynomialTensor a b) = determinantAdaptedTensor a b :=
    determinant_basis_change a b
  rwa [he] at h

/-- Coefficients are constant or linear in the degeneration parameter. -/
def determinantPolynomialFamily (a b : ℕ) :
    Tensor (Polynomial Coeff) (Fin (a + 1)) (Fin (b + 3) ⊕ Fin (b + 1))
      (Fin (a + b + 3) ⊕ Fin (a + b + 1)) :=
  weightedPolynomial (determinantAdaptedTensor a b) (fun _ => 0)
    (determinantInputWeight b) (determinantOutputWeight a b)

theorem determinantPolynomialFamily_coeff_zero (a b : ℕ) :
    (fun i y z => (determinantPolynomialFamily a b i y z).coeff 0) =
      determinantGradedTensor a b := by
  funext i y z
  rw [determinantPolynomialFamily, weightedPolynomial_coeff_zero
    (determinantAdaptedTensor a b) (fun _ => 0)
    (determinantInputWeight b) (determinantOutputWeight a b)
    (determinant_supported_weight a b)]
  exact congrFun (congrFun (congrFun (determinant_weightedLimit a b) i) y) z

theorem determinantPolynomialFamily_degree_le (a b : ℕ)
    (i : Fin (a + 1)) (y : Fin (b + 3) ⊕ Fin (b + 1))
    (z : Fin (a + b + 3) ⊕ Fin (a + b + 1)) :
    (determinantPolynomialFamily a b i y z).degree ≤ (1 : ℕ) := by
  apply weightedPolynomial_degree_le
  intro i' y' z' hc
  cases y' <;> cases z' <;>
    simp_all [determinantAdaptedTensor, determinantInputWeight, determinantOutputWeight]

theorem determinantPolynomialFamily_eval_mem_restrictionOrbit (a b : ℕ)
    {t : Coeff} (ht : t ≠ 0) :
    (fun i y z => (determinantPolynomialFamily a b i y z).eval t) ∈
      LocalTensor.orbit
        (Tensor.product (polynomialTensor (a + 1) (b + 2)) binaryDotTensor) := by
  have h := weightedPolynomial_eval_mem_restrictionOrbit
    (determinantAdaptedTensor a b) (fun _ => 0)
    (determinantInputWeight b) (determinantOutputWeight a b)
    (determinant_supported_weight a b) ht
  exact restrictionOrbit_trans (determinantAdapted_mem_restrictionOrbit a b) h

end OAI.LinearAlgebra.MatrixExponent.Upper

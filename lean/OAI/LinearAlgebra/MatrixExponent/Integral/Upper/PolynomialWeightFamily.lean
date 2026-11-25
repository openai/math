import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.Coefficients
import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.PolynomialDegeneration
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Eval.Coeff

open OAI.LinearAlgebra.MatrixExponent.Integral OAI.LinearAlgebra.TensorSpectrum

/-!
# Explicit polynomial families for diagonal weight degenerations

The diagonal degeneration has a polynomial coefficient family, not merely a
topological limit. Its constant coefficient is the retained tensor. Its degree
is controlled by the supported total weights. At every nonzero parameter its
evaluation is an exact restriction of the source tensor. These are the inputs
needed to extract tensor powers by finite interpolation.
-/

open OAI.MatrixMultiplication.Foundation

noncomputable section

namespace OAI.LinearAlgebra.MatrixExponent.Integral.Upper

variable {X Y Z : Type*}

/-- The monomial family associated to three integer coordinate weights. -/
def weightedPolynomial (T : Tensor O X Y Z)
    (wx : X → ℤ) (wy : Y → ℤ) (wz : Z → ℤ) :
    Tensor (Polynomial O) X Y Z :=
  fun x y z => Polynomial.monomial (wx x + wy y + wz z).toNat (T x y z)

/-- Polynomial evaluation agrees with the continuous coefficient family used
in the degeneration proof, including at the parameter zero. -/
theorem weightedPolynomial_eval (T : Tensor O X Y Z)
    (wx : X → ℤ) (wy : Y → ℤ) (wz : Z → ℤ) (t : O) :
    (fun x y z => (weightedPolynomial T wx wy wz x y z).eval t) =
      weightedFamily T wx wy wz t := by
  funext x y z
  simp [weightedPolynomial, weightedFamily, Polynomial.eval_monomial, mul_comm]

/-- The constant coefficient keeps precisely the supported weight-zero terms. -/
theorem weightedPolynomial_coeff_zero (T : Tensor O X Y Z)
    (wx : X → ℤ) (wy : Y → ℤ) (wz : Z → ℤ)
    (h : ∀ x y z, T x y z ≠ 0 → 0 ≤ wx x + wy y + wz z)
    (x : X) (y : Y) (z : Z) :
    (weightedPolynomial T wx wy wz x y z).coeff 0 =
      weightedLimit T wx wy wz x y z := by
  have heq := (weightedPolynomial_eval T wx wy wz 0).trans
    (weightedFamily_zero T wx wy wz h)
  simpa only [Polynomial.coeff_zero_eq_eval_zero] using
    congrFun (congrFun (congrFun heq x) y) z

/-- A degree bound is needed only on supported coefficients. Unsupported
coordinates are the zero polynomial, regardless of their assigned weights. -/
theorem weightedPolynomial_natDegree_le (T : Tensor O X Y Z)
    (wx : X → ℤ) (wy : Y → ℤ) (wz : Z → ℤ) {D : ℕ}
    (hD : ∀ x y z, T x y z ≠ 0 → (wx x + wy y + wz z).toNat ≤ D)
    (x : X) (y : Y) (z : Z) :
    (weightedPolynomial T wx wy wz x y z).natDegree ≤ D := by
  by_cases hT : T x y z = 0
  · simp [weightedPolynomial, hT]
  · exact (Polynomial.natDegree_monomial_le (T x y z)).trans (hD x y z hT)

/-- The same degree bound in the form used by polynomial interpolation. -/
theorem weightedPolynomial_degree_le (T : Tensor O X Y Z)
    (wx : X → ℤ) (wy : Y → ℤ) (wz : Z → ℤ) {D : ℕ}
    (hD : ∀ x y z, T x y z ≠ 0 → (wx x + wy y + wz z).toNat ≤ D)
    (x : X) (y : Y) (z : Z) :
    (weightedPolynomial T wx wy wz x y z).degree ≤ D :=
  Polynomial.degree_le_of_natDegree_le
    (weightedPolynomial_natDegree_le T wx wy wz hD x y z)

/-- A weight-zero/weight-one support split gives degree at most one. This is
the bound used by the determinant filtration and the three-sector split. -/
theorem weightedPolynomial_degree_le_one (T : Tensor O X Y Z)
    (wx : X → ℤ) (wy : Y → ℤ) (wz : Z → ℤ)
    (h : ∀ x y z, T x y z ≠ 0 →
      wx x + wy y + wz z = 0 ∨ wx x + wy y + wz z = 1)
    (x : X) (y : Y) (z : Z) :
    (weightedPolynomial T wx wy wz x y z).degree ≤ (1 : ℕ) := by
  apply weightedPolynomial_degree_le T wx wy wz
  intro u v w hT
  rcases h u v w hT with hw | hw <;> simp [hw]

/-- Every nonzero evaluation has actual diagonal local restriction witnesses;
the polynomial family does not assume a character or a continuity principle. -/
theorem weightedPolynomial_eval_mem_restrictionOrbit
    [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor O X Y Z) (wx : X → ℤ) (wy : Y → ℤ) (wz : Z → ℤ)
    (h : ∀ x y z, T x y z ≠ 0 → 0 ≤ wx x + wy y + wz z)
    {t : O} (ht : IsUnit t) :
    (fun x y z => (weightedPolynomial T wx wy wz x y z).eval t) ∈
      LocalTensor.orbit T := by
  rw [weightedPolynomial_eval]
  exact weightedFamily_mem_restrictionOrbit T wx wy wz h ht

/-- Actual local restriction witnesses compose without a limiting argument. -/
theorem restrictionOrbit_trans
    {X' Y' Z' X'' Y'' Z'' : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z']
    {T : Tensor O X Y Z} {U : Tensor O X' Y' Z'} {V : Tensor O X'' Y'' Z''}
    (hTU : U ∈ LocalTensor.orbit T)
    (hUV : V ∈ LocalTensor.orbit U) :
    V ∈ LocalTensor.orbit T := by
  rcases hTU with ⟨A, B, C, rfl⟩
  rcases hUV with ⟨D, E, F, rfl⟩
  exact ⟨Tensor.composeRestrictionMatrix D A, Tensor.composeRestrictionMatrix E B,
    Tensor.composeRestrictionMatrix F C, Tensor.restrict_restrict A B C D E F T⟩

end OAI.LinearAlgebra.MatrixExponent.Integral.Upper

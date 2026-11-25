import OAI.LinearAlgebra.FiniteFourier.ToeplitzCirculant
import OAI.LinearAlgebra.FiniteFourier.ArithmeticSpecialization
import OAI.Computability.FourierCircuit.Triangular

/-! # Specialization of polynomial multiplication to fixed Toeplitz maps

A length-`n` program for the formal product has one output for each of the
`2*n-1` possible coefficients. Pinning its second operand gives all rows of a
fixed convolution at the same binary-gate budget. Reading the low coefficients
gives the triangular Toeplitz map, and reading the middle coefficients of a
padded product gives arbitrary signed offsets.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open MvPolynomial OAI.LinearAlgebra.SpectralBooks
open scoped BigOperators

/-- The coefficient of degree `d` in the product of two generic polynomials of length `n`. -/
noncomputable def convolutionCoefficient (R : Type*) [CommRing R] (n d : ℕ) :
    MvPolynomial (Fin n ⊕ Fin n) R :=
  ∑ i : Fin n, X (.inl i) *
    ∑ j : Fin n, if i.val + j.val = d then X (.inr j) else 0

/-- The defining bilinear form agrees with taking the coefficient of the ordinary
univariate polynomial product. -/
theorem convolutionCoefficient_eq_coeff (R : Type*) [CommRing R] (n d : ℕ) :
    convolutionCoefficient R n d =
      ((∑ i : Fin n, Polynomial.monomial i.val (X (.inl i) : MvPolynomial (Fin n ⊕ Fin n) R)) *
        (∑ j : Fin n, Polynomial.monomial j.val (X (Sum.inr j) : MvPolynomial (Fin n ⊕ Fin n) R))).coeff d := by
  classical
  simp only [convolutionCoefficient, Finset.sum_mul, Finset.mul_sum, Polynomial.finsetSum_coeff,
    Polynomial.monomial_mul_monomial, Polynomial.coeff_monomial, mul_ite, mul_zero]
  rw [Finset.sum_comm]

variable {R K : Type*} [CommRing R]
/-- At a fixed right operand the left-input block of the Jacobian is the
ordinary convolution matrix. -/
theorem derivativeRow_convolution_left [CommRing K] (φ : R →+* K) {n : ℕ} (y : Fin n → K) (d : ℕ)
    (i : Fin n) :
    derivativeRow φ (Sum.elim (fun _ => 0) y) (convolutionCoefficient R n d) (.inl i) =
      ∑ j : Fin n, if i.val + j.val = d then y j else 0 := by
  classical
  simp only [derivativeRow, convolutionCoefficient, map_sum, pderiv_mul, map_add, map_mul,
    eval₂Hom_X', Sum.elim_inl, zero_mul, add_zero, pderiv_X, Pi.single_apply]
  rw [Finset.sum_eq_single i]
  · simp [apply_ite]
  · intro j _ hj
    simp [hj]
  · simp

/-- Correctness in the coefficient ring before specialization to any target field. -/
def ComputesConvolution {n r : ℕ}
    (P : MatrixMultiplication.Arithmetic.Program R (Fin n ⊕ Fin n) r)
    (out : Fin (2*n-1) → Fin r) : Prop :=
  ∀ d, registerPolynomial P (out d) = convolutionCoefficient R n d.val

variable [Field K]

/-- The pinned convolution applied to the first operand. -/
def fixedConvolutionMatrix {n : ℕ} (y : Fin n → K) : Matrix (Fin (2*n-1)) (Fin n) K :=
  fun d i => ∑ j, if i.val + j.val = d.val then y j else 0

/-- Specializing a shared formal multiplication program produces a shared linear
circuit of no greater cost for all coefficients of fixed convolution. -/
theorem ComputesConvolution.realizable_fixed {n r : ℕ}
    {P : MatrixMultiplication.Arithmetic.Program R (Fin n ⊕ Fin n) r}
    {out : Fin (2*n-1) → Fin r} (hP : ComputesConvolution P out) (φ : R →+* K) (y : Fin n → K) :
    RealizableAtMost (fixedConvolutionMatrix y) P.cost := by
  have h := (realizableAtMost_jacobian φ (Sum.elim (fun _ => 0) y) P out).submatrix id
    (Function.Embedding.inl : Fin n ↪ Fin n ⊕ Fin n)
  convert h using 1
  ext d i
  change _ = derivativeRow φ _ (registerPolynomial P (out d)) (.inl i)
  rw [hP d, derivativeRow_convolution_left]
  rfl

private theorem fixedConvolutionMatrix_apply {n : ℕ} (y : Fin n → K)
    (d : Fin (2*n-1)) (i : Fin n) :
    fixedConvolutionMatrix y d i =
      if h : i.val ≤ d.val ∧ d.val-i.val < n then y ⟨d.val-i.val, h.2⟩ else 0 := by
  classical
  unfold fixedConvolutionMatrix
  split_ifs with h
  · let k : Fin n := ⟨d.val-i.val, h.2⟩
    rw [Finset.sum_eq_single k]
    · simp [k, Nat.add_sub_of_le h.1]
    · intro j _ hj
      apply ite_eq_right
      intro he
      apply hj
      apply Fin.ext
      change j.val = d.val - i.val
      omega
    · simp
  · apply Finset.sum_eq_zero
    intro j _
    apply ite_eq_right
    intro he
    apply h
    have := j.isLt
    omega

/-- Reading the low coefficients of length-`n` multiplication gives the lower
triangular Toeplitz matrix of any power series, with the same gate count. -/
theorem ComputesConvolution.realizable_truncMatrix {n r : ℕ}
    {P : MatrixMultiplication.Arithmetic.Program R (Fin n ⊕ Fin n) r}
    {out : Fin (2*n-1) → Fin r} (hP : ComputesConvolution P out) (φ : R →+* K)
    (f : PowerSeries K) : RealizableAtMost (ExactFourier.CoefficientTime.truncMatrix n f) P.cost := by
  let low (i : Fin n) : Fin (2*n-1) := ⟨i.val, by have := i.isLt; omega⟩
  have h := (hP.realizable_fixed φ (fun j => PowerSeries.coeff j.val f)).submatrix low
    (Function.Embedding.refl (Fin n))
  convert h using 1
  ext i j
  simp only [ExactFourier.CoefficientTime.truncMatrix, Matrix.submatrix_apply,
    Function.Embedding.refl_apply, fixedConvolutionMatrix_apply, low]
  split_ifs <;> first | rfl | (exfalso; have := i.isLt; omega)

/-- Reading the middle coefficients after zero padding realizes every square
Toeplitz matrix from a length-`2*a` multiplication program. This applies in
particular to an integral program via the canonical map into any field. -/
theorem ComputesConvolution.realizable_toeplitz {a r : ℕ}
    {P : MatrixMultiplication.Arithmetic.Program R (Fin (2*a) ⊕ Fin (2*a)) r}
    {out : Fin (2*(2*a)-1) → Fin r} (hP : ComputesConvolution P out)
    (φ : R →+* K) (c : ℤ → K) : RealizableAtMost (toeplitzOfOffsets a c) P.cost := by
  let middle (i : Fin a) : Fin (2*(2*a)-1) := ⟨a+i.val, by have := i.isLt; omega⟩
  let y (j : Fin (2*a)) := c ((j.val : ℤ)-a)
  have h := (hP.realizable_fixed φ y).submatrix middle (Fin.castLEEmb (by omega : a ≤ 2*a))
  convert h using 1
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  have hk : j.val ≤ a+i.val ∧ a+i.val-j.val < 2*a := by omega
  simp only [toeplitzOfOffsets, Matrix.submatrix_apply, fixedConvolutionMatrix_apply,
    middle, Fin.castLEEmb_apply, Fin.val_castLE, hk, y]
  congr 1
  omega

end FiniteFourier
end LinearAlgebra
end OAI

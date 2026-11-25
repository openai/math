import OAI.Computability.NearSquareRoot.SynchronizedChirp
import OAI.Computability.NearSquareRoot.SynchronizedTensor
import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Spectral phase diagonal for restoring a short transform

The chirp circulant is diagonal in the same positive-sign Fourier coordinates
as the short transform. All entries of its spectral diagonal are unit phases.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier

open ComplexConjugate Matrix Finset

noncomputable section

variable {a : ℕ} [NeZero a]

def finChar (a : ℕ) [NeZero a] (x : Fin a) : ℂ :=
  ZMod.stdAddChar (ZMod.finEquiv a x)

private theorem finChar_add (x y : Fin a) :
    finChar a (x+y) = finChar a x * finChar a y := by
  simp [finChar, AddChar.map_add_eq_mul]

theorem finEquiv_val (j : Fin a) : ZMod.finEquiv a j = (j.val : ZMod a) := by
  rw [← ZMod.natCast_zmod_val (ZMod.finEquiv a j)]
  apply congrArg
  cases a with
  | zero => exact Fin.elim0 j
  | succ a => rfl

/-- The chirp factorization uses the same axis operator as the padded tensor. -/
theorem normalizedFourier_axisMatrix :
    normalizedFourier a = (ResidueFourier.axisMatrix a).submatrix (ZMod.finEquiv a) (ZMod.finEquiv a) := by
  ext j h
  simp only [ResidueFourier.axisMatrix, Matrix.submatrix_apply, Matrix.of_apply, finEquiv_val]
  rw [show (h.val : ZMod a) * (j.val : ZMod a) = ((h.val * j.val : ℤ) : ZMod a) by push_cast; rfl,
    ZMod.stdAddChar_coe]
  unfold normalizedFourier phase
  push_cast
  congr 2
  ring

private theorem fourier_char_entry (j h : Fin a) :
    normalizedFourier a j h = (Real.sqrt a : ℂ)⁻¹ * finChar a (j*h) := by
  rw [normalizedFourier_axisMatrix]
  simp [ResidueFourier.axisMatrix, finChar, mul_comm]

/-- Unitarity of the normalized positive-sign short transform, on its actual fiber. -/
theorem normalizedFourier_unitary : normalizedFourier a ∈ unitary (Matrix (Fin a) (Fin a) ℂ) := by
  let e := (ZMod.finEquiv a).toEquiv
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, normalizedFourier_axisMatrix,
    Matrix.conjTranspose_submatrix]
  change (_ : Matrix (ZMod a) (ZMod a) ℂ).submatrix e e * (_ : Matrix (ZMod a) (ZMod a) ℂ).submatrix e e = 1
  rw [Matrix.submatrix_mul_equiv _ _ _ e _, ResidueFourier.axisMatrix_unitary, Matrix.submatrix_one_equiv]

/-- Kernel of the circulant acting on one occupied fiber. -/
def chirpKernel (a : ℕ) (t : Fin a) : ℂ := (Real.sqrt a : ℂ)⁻¹ * conj (chirp a t.val)

private theorem chirpCirculant_eq : chirpCirculant a = circulant (chirpKernel a) := by
  ext j h
  simp only [chirpCirculant, circulant_apply, chirpKernel, Fin.intCast_val_sub_eq_sub_add_ite,
    chirp_emod (NeZero.pos a)]
  split_ifs <;> simp [chirp_periodic (NeZero.pos a) _]

/-- Positive-sign Fourier character of a product of two residue indices, in turns. -/
theorem finChar_mul_phase (j t : Fin a) : finChar a (j * t) = phase ((j.val : ℝ) * t.val / a) := by
  have eq := fourier_char_entry j t
  change (Real.sqrt a : ℂ)⁻¹ * phase _ = _ at eq
  exact mul_left_cancel₀ (inv_ne_zero (by exact_mod_cast Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr (NeZero.pos a)))) eq.symm

/-- Diagonal eigenvalue of a circular difference kernel at a given frequency. -/
def circulantSpectrum (v : Fin a → ℂ) (j : Fin a) : ℂ :=
  ∑ t, v t * phase ((j.val : ℝ) * t.val / a)

/-- Fourier transformation of an arbitrary circulant with kernel `v` is pointwise
multiplication by the unnormalized positive-sign transform of the kernel. -/
theorem fourier_intertwines_circulant (v : Fin a → ℂ) :
    normalizedFourier a * circulant v = diagonal (circulantSpectrum v) * normalizedFourier a := by
  ext j h
  rw [Matrix.diagonal_mul, Matrix.mul_apply, fourier_char_entry]
  simp only [fourier_char_entry, circulant_apply, circulantSpectrum, ← finChar_mul_phase, Finset.sum_mul]
  refine Fintype.sum_equiv (Equiv.subRight h) _ _ fun z => ?_
  simp only [Equiv.subRight_apply]
  rw [show finChar a (j*z) = finChar a (j*(z-h)) * finChar a (j*h) by
    rw [← finChar_add, ← mul_add, sub_add_cancel]]
  ring

/-- Conjugation by the forward transform diagonalizes any cyclic difference kernel. -/
theorem circulant_spectral_diagonal (v : Fin a → ℂ) :
    normalizedFourier a * circulant v * (normalizedFourier a)ᴴ = diagonal (circulantSpectrum v) := by
  rw [fourier_intertwines_circulant, mul_assoc, ← Matrix.star_eq_conjTranspose,
    normalizedFourier_unitary.2, mul_one]

/-- Phase table used between the two restored circuits. -/
def chirpSpectrum (a : ℕ) [NeZero a] := circulantSpectrum (chirpKernel a)

/-- `D₂ = U C U*`, including the explicit finite sum for the diagonal. -/
theorem chirp_spectral_diagonal :
    normalizedFourier a * chirpCirculant a * (normalizedFourier a)ᴴ = diagonal (chirpSpectrum a) := by
  rw [chirpCirculant_eq, circulant_spectral_diagonal]
  rfl

omit [NeZero a] in
private theorem chirp_diag_unitary (f : Fin a → ℤ) :
    diagonal (fun j => chirp a (f j)) ∈ unitary (Matrix (Fin a) (Fin a) ℂ) := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  apply congrArg
  funext j
  change chirp a (f j) * conj (chirp a (f j)) = 1
  unfold chirp
  rw [phase_conj]
  exact mul_inv_cancel₀ (Complex.exp_ne_zero _)

private theorem chirpCirculant_unitary : chirpCirculant a ∈ unitary (Matrix (Fin a) (Fin a) ℂ) := by
  let D₁ := Matrix.diagonal (fun j : Fin a => chirp a j.val)
  let D₃ := Matrix.diagonal (fun h : Fin a => chirp a (-(h.val : ℤ)))
  have h₁ : D₁ ∈ unitary _ := chirp_diag_unitary _
  have h₃ : D₃ ∈ unitary _ := chirp_diag_unitary _
  have eq : normalizedFourier a = D₁ * chirpCirculant a * D₃ := normalizedFourier_factorization (NeZero.pos a)
  have inv : star D₁ * normalizedFourier a * star D₃ = chirpCirculant a := by
    rw [eq, ← mul_assoc, ← mul_assoc, h₁.1, one_mul, mul_assoc, h₃.2, mul_one]
  rw [← inv]
  exact (unitary _).mul_mem ((unitary _).mul_mem (Unitary.star_mem h₁) normalizedFourier_unitary) (Unitary.star_mem h₃)

/-- The spectral table is phase-only, including for even axis lengths. -/
theorem chirpSpectrum_norm (j : Fin a) : ‖chirpSpectrum a j‖ = 1 := by
  have h : diagonal (chirpSpectrum a) ∈ unitary (Matrix (Fin a) (Fin a) ℂ) := by
    rw [← chirp_spectral_diagonal, ← Matrix.star_eq_conjTranspose]
    exact (unitary _).mul_mem ((unitary _).mul_mem normalizedFourier_unitary chirpCirculant_unitary)
      (Unitary.star_mem normalizedFourier_unitary)
  have eq := h.2
  rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal] at eq
  have val := congrArg (fun M : Matrix (Fin a) (Fin a) ℂ => M j j) eq
  simp only [Matrix.diagonal_apply_eq, Pi.star_apply, Matrix.one_apply_eq,
    Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow] at val
  have hs : ‖chirpSpectrum a j‖^2 = (1 : ℝ) := by exact_mod_cast val
  nlinarith [norm_nonneg (chirpSpectrum a j)]

end
end ShortFourier

end NearSquareRoot
end Computability
end OAI

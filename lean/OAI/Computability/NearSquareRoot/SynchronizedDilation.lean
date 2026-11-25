import OAI.Computability.NearSquareRoot.SynchronizedComplement
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! # Dilation of the short chirp convolution

Take a forward Fourier transform in the first half of the ambient array,
apply one two-coordinate dilation per frequency, then undo that transform.
Its compression to the first half is precisely the scaled circulant.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier

open Matrix ComplexConjugate
open scoped Matrix
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def dilationOffDiagonal (z : ℂ) : ℂ := Real.sqrt (1 - ‖z‖ ^ 2)

/-- The `i`th inl and inr coordinates form a single pair with diagonal entry `z i`. -/
def dilation (z : ι → ℂ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
  let d := fun i => dilationOffDiagonal (z i)
  fromBlocks (diagonal z) (diagonal d) (diagonal d) (diagonal fun i => -conj (z i))

theorem dilation_isometry (z : ι → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) :
    (dilation z)ᴴ * dilation z = 1 := by
  have hoff (i : ι) : dilationOffDiagonal (z i) ^ 2 = 1 - (‖z i‖ : ℂ)^2 := by
    have hr := mul_self_le_mul_self (norm_nonneg (z i)) (hz i)
    have h : 0 ≤ 1 - ‖z i‖^2 := by nlinarith
    unfold dilationOffDiagonal
    exact_mod_cast Real.sq_sqrt h
  have hs (i : ι) : star (dilationOffDiagonal (z i)) = dilationOffDiagonal (z i) := by
    simp [dilationOffDiagonal]
  rw [dilation, fromBlocks_conjTranspose, fromBlocks_multiply, ← fromBlocks_one]
  congr 1 <;> apply Matrix.ext <;> intro i j <;> by_cases h : i = j
  all_goals try { simp [h, one_apply] }
  all_goals subst j
  all_goals (simp [hs]; ring_nf)
  · rw [hoff, Complex.conj_mul']
    ring
  · rw [hoff, Complex.mul_conj']
    ring

/-- Apply a Fourier matrix on the first half and leave the second half untouched. -/
def firstHalf (F : Matrix ι ι ℂ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
  fromBlocks F 0 0 1

theorem firstHalf_isometry (F : Matrix ι ι ℂ) (h : Fᴴ * F = 1) :
    (firstHalf F)ᴴ * firstHalf F = 1 := by
  simp [firstHalf, fromBlocks_conjTranspose, fromBlocks_multiply, h]

/-- Conjugate the local pairs by the Fourier transform on the occupied half. -/
def dilatedConvolution (F : Matrix ι ι ℂ) (z : ι → ℂ) :=
  (firstHalf F)ᴴ * dilation z * firstHalf F

theorem dilatedConvolution_isometry (F : Matrix ι ι ℂ) (hF : Fᴴ * F = 1)
    (hF' : F * Fᴴ = 1) (z : ι → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) :
    (dilatedConvolution F z)ᴴ * dilatedConvolution F z = 1 := by
  have h' : firstHalf F * (firstHalf F)ᴴ = 1 := by
    simp [firstHalf, fromBlocks_conjTranspose, fromBlocks_multiply, hF']
  simp only [dilatedConvolution, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc,
    ← Matrix.mul_assoc (firstHalf F) (firstHalf F)ᴴ, h', Matrix.one_mul,
    ← Matrix.mul_assoc (dilation z)ᴴ (dilation z), dilation_isometry z hz,
    firstHalf_isometry F hF]

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Embed active coordinates on the first tape half with zero borrowed coordinates. -/
def firstHalfInclusion (E : Matrix ι κ ℂ) : Matrix (ι ⊕ ι) κ ℂ :=
  fromRows E 0

omit [DecidableEq ι] [Fintype κ] in
theorem firstHalfInclusion_isometry (E : Matrix ι κ ℂ) (hE : Eᴴ * E = 1) :
    (firstHalfInclusion E)ᴴ * firstHalfInclusion E = 1 := by
  simp [firstHalfInclusion, conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromRows, hE]

omit [DecidableEq κ] [Fintype κ] in
theorem compress_dilatedConvolution (F : Matrix ι ι ℂ) (E : Matrix ι κ ℂ) (z : ι → ℂ) :
    (firstHalfInclusion E)ᴴ * dilatedConvolution F z * firstHalfInclusion E =
      Eᴴ * (Fᴴ * diagonal z * F) * E := by
  simp [dilatedConvolution, firstHalf, dilation, firstHalfInclusion,
    conjTranspose_fromRows_eq_fromCols_conjTranspose, fromBlocks_conjTranspose,
    fromBlocks_multiply, fromCols_mul_fromBlocks, fromCols_mul_fromRows, Matrix.mul_assoc]


omit [Fintype ι] in
theorem extend_adjoint (E : Matrix ι κ ℂ) (D : Matrix κ κ ℂ) :
    (extend E D)ᴴ = extend E Dᴴ := by
  simp only [extend, conjTranspose_add, conjTranspose_one, conjTranspose_mul,
    conjTranspose_sub, conjTranspose_conjTranspose, Matrix.mul_assoc]

theorem extend_isometry (E : Matrix ι κ ℂ) (D : Matrix κ κ ℂ) (hE : Eᴴ * E = 1)
    (hD : Dᴴ * D = 1) : (extend E D)ᴴ * extend E D = 1 := by
  rw [extend_adjoint, extend_mul _ hE, hD]
  simp [extend]

/-- The two chirp diagonals are applied only on the active fiber before and after
the unitary dilation. -/
def chirpDilation (F : Matrix ι ι ℂ) (z : ι → ℂ) (E : Matrix ι κ ℂ)
    (L R : Matrix κ κ ℂ) :=
  let A := firstHalfInclusion E
  extend A L * dilatedConvolution F z * extend A R

theorem chirpDilation_isometry (F : Matrix ι ι ℂ) (z : ι → ℂ) (E : Matrix ι κ ℂ)
    (L R : Matrix κ κ ℂ) (hF : Fᴴ * F = 1) (hF' : F * Fᴴ = 1) (hz : ∀ i, ‖z i‖ ≤ 1)
    (hE : Eᴴ * E = 1) (hL : Lᴴ * L = 1) (hR : Rᴴ * R = 1) :
    (chirpDilation F z E L R)ᴴ * chirpDilation F z E L R = 1 := by
  let A := firstHalfInclusion E
  have hA := firstHalfInclusion_isometry E hE
  change (extend A L * dilatedConvolution F z * extend A R)ᴴ * (extend A L * dilatedConvolution F z * extend A R) = 1
  simp only [conjTranspose_mul,
    Matrix.mul_assoc, ← Matrix.mul_assoc (extend A L)ᴴ (extend A L), extend_isometry A L hA hL,
    Matrix.one_mul, ← Matrix.mul_assoc (dilatedConvolution F z)ᴴ (dilatedConvolution F z),
    dilatedConvolution_isometry F hF hF' z hz, extend_isometry A R hA hR]

theorem compress_chirpDilation (F : Matrix ι ι ℂ) (z : ι → ℂ) (E : Matrix ι κ ℂ)
    (L R : Matrix κ κ ℂ) (hE : Eᴴ * E = 1) :
    (firstHalfInclusion E)ᴴ * chirpDilation F z E L R * firstHalfInclusion E =
      L * (Eᴴ * (Fᴴ * diagonal z * F) * E) * R := by
  let A := firstHalfInclusion E
  have hA := firstHalfInclusion_isometry E hE
  have hleft : Aᴴ * extend A L = L * Aᴴ := by
    simpa only [conjTranspose_mul, conjTranspose_conjTranspose, extend_adjoint]
      using congrArg Matrix.conjTranspose (extend_on_fiber A hA Lᴴ)
  change Aᴴ * (extend A L * dilatedConvolution F z * extend A R) * A = _
  calc
    _ = (Aᴴ * extend A L) * dilatedConvolution F z * (extend A R * A) := by simp only [Matrix.mul_assoc]
    _ = L * (Aᴴ * dilatedConvolution F z * A) * R := by
      rw [hleft, extend_on_fiber A hA]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [compress_dilatedConvolution]

end
end ShortFourier

end NearSquareRoot
end Computability
end OAI

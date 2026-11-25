import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Analysis.Complex.Order
import Mathlib.Tactic.Module
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-! # Exact amplification of a compressed short Fourier transform

The rectangular matrices `X` and `Y` embed the same active input fiber in the
ambient space, before and after the desired unitary, respectively. Reflection
in their images acts by a planar rotation. All the formulas are identities on
the whole fiber, including linear combinations of its coordinate vectors.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace SynchronizedRestoration

open Matrix
open scoped Matrix ComplexOrder

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Product of the reflection in the first image and the negative reflection
in the second image, in order of matrix action. -/
noncomputable def reflectPair (X Y : Matrix m n ℂ) : Matrix m m ℂ :=
  ((2 : ℝ) • (X * Xᴴ) - 1) * (1 - (2 : ℝ) • (Y * Yᴴ))

/-- The two real amplitudes after an arbitrary number of applications. The
factor `cos φ` avoids a division even in the degenerate angle cases. -/
theorem rotation (X Y : Matrix m n ℂ) (φ : ℝ)
    (hX : Xᴴ * X = 1) (hY : Yᴴ * Y = 1)
    (hYX : Yᴴ * X = Real.sin φ • 1) (j : ℕ) :
    Real.cos φ • ((reflectPair X Y)^j * X) =
      Real.cos ((2 * (j : ℝ) + 1) * φ) • X + Real.sin (2 * j * φ) • Y := by
  have hXY : Xᴴ * Y = Real.sin φ • 1 := by
    simpa using congrArg Matrix.conjTranspose hYX
  have hx : reflectPair X Y * X =
      (1 - 4 * (Real.sin φ)^2) • X + (2 * Real.sin φ) • Y := by
    simp only [reflectPair, Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul,
      Matrix.smul_mul, Matrix.mul_sub, Matrix.mul_smul, hX, hXY, hYX, Matrix.mul_one]
    module
  have hy : reflectPair X Y * Y = (-2 * Real.sin φ) • X + Y := by
    simp only [reflectPair, Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul,
      Matrix.smul_mul, Matrix.mul_sub, Matrix.mul_smul, hY, hXY, Matrix.mul_one]
    module
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', Matrix.mul_assoc, ← Matrix.mul_smul, ih, Matrix.mul_add,
      Matrix.mul_smul, Matrix.mul_smul, hx, hy]
    push_cast
    set θ := 2 * (j : ℝ) * φ
    rw [show (2 * (j : ℝ) + 1) * φ = θ + φ by dsimp [θ]; ring,
      show (2 * ((j : ℝ) + 1) + 1) * φ = θ + φ + (φ + φ) by dsimp [θ]; ring,
      show 2 * ((j : ℝ) + 1) * φ = θ + (φ + φ) by dsimp [θ]; ring]
    simp only [Real.cos_add, Real.sin_add]
    match_scalars
    · linear_combination (3 * Real.sin θ * Real.sin φ - Real.cos θ * Real.cos φ) *
        Real.sin_sq_add_cos_sq φ
    · linear_combination -Real.sin θ * Real.sin_sq_add_cos_sq φ

/-- With the prescribed initial angle, the final reflection lands exactly on
the target embedding. -/
theorem amplify (X Y : Matrix m n ℂ) (j : ℕ)
    (hX : Xᴴ * X = 1) (hY : Yᴴ * Y = 1)
    (hYX : Yᴴ * X = Real.sin (Real.pi / (4 * (j : ℝ) + 2)) • 1) :
    (reflectPair X Y)^j * X = Y := by
  set φ := Real.pi / (4 * (j : ℝ) + 2)
  by_cases hj : j = 0
  · subst j
    have hYX' : Yᴴ * X = 1 := by simpa [φ] using hYX
    have hXY : Xᴴ * Y = 1 := by simpa using congrArg Matrix.conjTranspose hYX'
    have hpos : (X - Y)ᴴ * (X - Y) = 0 := by
      simp [Matrix.sub_mul, Matrix.mul_sub, hX, hY, hXY, hYX']
    simpa using sub_eq_zero.mp (Matrix.conjTranspose_mul_self_eq_zero.mp hpos)
  have hφ : 0 < φ := by dsimp [φ]; positivity
  have hlt : φ < Real.pi / 2 := by
    dsimp [φ]
    gcongr
    exact_mod_cast (by omega : 2 < 4 * j + 2)
  have hcos : Real.cos φ ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hlt⟩).ne'
  have hangle : (2 * (j : ℝ) + 1) * φ = Real.pi / 2 := by
    dsimp [φ]
    field_simp
    ring
  have hsin : Real.sin (2 * j * φ) = Real.cos φ := by
    rw [show 2 * (j : ℝ) * φ = Real.pi / 2 - φ by linarith [hangle], Real.sin_sub]
    simp
  have h := rotation X Y φ hX hY hYX j
  rw [hangle, Real.cos_pi_div_two, zero_smul, zero_add, hsin] at h
  exact (smul_right_injective _ hcos) h


/-- Compression of a unitary by the active coordinates. Applying the two
reflections `j` times recovers the desired unitary exactly on those coordinates.
`E` may be any isometric inclusion of the active block. -/
theorem amplify_compression (E : Matrix m n ℂ) (V : Matrix m m ℂ) (U : Matrix n n ℂ)
    (j : ℕ) (hE : Eᴴ * E = 1) (hV : Vᴴ * V = 1) (hU : Uᴴ * U = 1)
    (hU' : U * Uᴴ = 1)
    (hc : Eᴴ * V * E = Real.sin (Real.pi / (4 * (j : ℝ) + 2)) • U) :
    (((2 : ℝ) • (V * (E * Eᴴ) * Vᴴ) - 1) * (1 - (2 : ℝ) • (E * Eᴴ)))^j *
      V * E = E * U := by
  set φ := Real.pi / (4 * (j : ℝ) + 2)
  have hX : (V * E)ᴴ * (V * E) = 1 := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ, hV,
      Matrix.one_mul, hE]
  have hY : (E * U)ᴴ * (E * U) = 1 := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Eᴴ, hE,
      Matrix.one_mul, hU]
  have hYX : (E * U)ᴴ * (V * E) = Real.sin φ • 1 := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Eᴴ, hc,
      Matrix.mul_smul, hU]
  have h := amplify (V * E) (E * U) j hX hY hYX
  have outside : E * U * (E * U)ᴴ = E * Eᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc U, hU', Matrix.one_mul]
  have inside : V * E * (V * E)ᴴ = V * (E * Eᴴ) * Vᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [reflectPair, outside, inside] at h
  rw [Matrix.mul_assoc _ V E]
  exact h

end SynchronizedRestoration

end NearSquareRoot
end Computability
end OAI

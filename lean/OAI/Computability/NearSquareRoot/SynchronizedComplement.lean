import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NoncommRing

/-!
# Restoring borrowed coordinates of a short Fourier transform

A rectangular isometry embeds the active Fourier fiber into the borrowed coordinate
space. Conjugating an extended phase diagonal by the amplified unitary cancels its
unknown action on the orthogonal complement.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier

open scoped Matrix

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Extend an operator on the embedded fiber by identity on its orthogonal complement. -/
def extend (E : Matrix κ ι ℂ) (D : Matrix ι ι ℂ) : Matrix κ κ ℂ :=
  1 + E * (D - 1) * Eᴴ

/-- The original coordinates receive precisely the operator supplied on the fiber. -/
theorem extend_on_fiber (E : Matrix κ ι ℂ) (hE : Eᴴ * E = 1) (D : Matrix ι ι ℂ) :
    extend E D * E = E * D := by
  rw [extend, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc _ Eᴴ E, hE, Matrix.mul_one,
    Matrix.mul_sub, Matrix.mul_one]
  abel

/-- For vectors on the borrowed complement, the extended circuit is the identity. -/
theorem extend_on_complement (E : Matrix κ ι ℂ) (D : Matrix ι ι ℂ) (v : κ → ℂ)
    (hv : Eᴴ *ᵥ v = 0) : extend E D *ᵥ v = v := by
  simp [extend, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hv]

theorem extend_mul (E : Matrix κ ι ℂ) (hE : Eᴴ * E = 1) (D F : Matrix ι ι ℂ) :
    extend E D * extend E F = extend E (D * F) := by
  unfold extend
  simp only [add_mul, mul_add, one_mul, mul_one]
  have hprod : E * (D - 1) * Eᴴ * (E * (F - 1) * Eᴴ) =
      E * ((D - 1) * (F - 1)) * Eᴴ := by
    simp [Matrix.mul_assoc, ← Matrix.mul_assoc Eᴴ E, hE]
  rw [hprod]
  have hsum : (D - 1) + (F - 1) + (D - 1) * (F - 1) = D * F - 1 := by
    noncomm_ring
  rw [← hsum]
  simp only [Matrix.mul_add, Matrix.add_mul]
  abel

/-- Conjugating an extended diagonal by a unitary uses only its restriction to the fiber. -/
theorem conjugate_extend (E : Matrix κ ι ℂ) (B : Matrix κ κ ℂ) (U D : Matrix ι ι ℂ)
    (hB : Bᴴ * B = 1) (hU : U * Uᴴ = 1) (h : B * E = E * U) :
    Bᴴ * extend E D * B = extend E (Uᴴ * D * U) := by
  have hleft : Bᴴ * E = E * Uᴴ := calc
    Bᴴ * E = Bᴴ * (E * U * Uᴴ) := by rw [Matrix.mul_assoc, hU, Matrix.mul_one]
    _ = E * Uᴴ := by rw [← h, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hB, Matrix.one_mul]
  have hright : Eᴴ * B = U * Eᴴ := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      using congrArg Matrix.conjTranspose hleft
  have hU' : Uᴴ * U = 1 := mul_eq_one_comm.mp hU
  unfold extend
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, hB]
  congr 1
  have hcore : Uᴴ * (D - 1) * U = Uᴴ * D * U - 1 := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, hU']
  rw [← hcore]
  calc
    Bᴴ * (E * (D - 1) * Eᴴ) * B = (Bᴴ * E) * (D - 1) * (Eᴴ * B) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [hleft, hright]; simp only [Matrix.mul_assoc]

/-- Three extended phase diagonals and a pair of amplified unitaries implement
the desired transform while restoring every borrowed coordinate. -/
theorem restore_complement (E : Matrix κ ι ℂ) (B : Matrix κ κ ℂ)
    (U D₁ D₂ D₃ : Matrix ι ι ℂ) (hE : Eᴴ * E = 1) (hB : Bᴴ * B = 1)
    (hU : U * Uᴴ = 1) (h : B * E = E * U)
    (hfactor : D₁ * (Uᴴ * D₂ * U) * D₃ = U) :
    extend E D₁ * Bᴴ * extend E D₂ * B * extend E D₃ = extend E U := by
  calc
    _ = extend E D₁ * (Bᴴ * extend E D₂ * B) * extend E D₃ := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [conjugate_extend E B U D₂ hB hU h, extend_mul E hE, extend_mul E hE, hfactor]

end ShortFourier

end NearSquareRoot
end Computability
end OAI

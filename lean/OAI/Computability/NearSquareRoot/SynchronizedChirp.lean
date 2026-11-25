import Mathlib.Algebra.Ring.Periodic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

/-! # Periodic chirps for exact restoration of a short Fourier transform -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier

open ComplexConjugate

noncomputable section

/-- Phase measured in turns. -/
def phase (x : ℝ) : ℂ := Complex.exp (x * (2 * (Real.pi : ℂ) * Complex.I))

theorem phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  simp [phase, add_mul, Complex.exp_add]

theorem phase_sub (x y : ℝ) : phase (x - y) = phase x / phase y := by
  simp [phase, sub_mul, Complex.exp_sub]

theorem phase_int (t : ℤ) : phase (t : ℝ) = 1 := by
  simp [phase, Complex.exp_int_mul_two_pi_mul_I]

theorem phase_conj (x : ℝ) : conj (phase x) = (phase x)⁻¹ := by
  rw [phase, ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  norm_num
  left
  exact map_ofNat _ 2

/-- The linear correction is required at odd transform lengths. -/
def chirpAngle (a : ℕ) (t : ℤ) : ℝ :=
  ((t : ℝ)^2 + (a % 2 : ℕ) * t) / (2 * a)

def chirp (a : ℕ) (t : ℤ) : ℂ := phase (chirpAngle a t)

/-- Translating by the transform length changes the angle by an integer. -/
theorem chirp_periodic {a : ℕ} (ha : 0 < a) : Function.Periodic (chirp a) (a : ℤ) := by
  intro t
  let q := (a + 1) / 2
  have he : (2 : ℕ) * q = a + a % 2 := by dsimp [q]; omega
  have hr : (2 : ℝ) * (q : ℝ) = (a : ℝ) + (a % 2 : ℕ) := by
    exact_mod_cast he
  have hangle : chirpAngle a (t + a) =
      chirpAngle a t + ((t + (q : ℤ) : ℤ) : ℝ) := by
    unfold chirpAngle
    push_cast
    field_simp
    nlinarith [congrArg (fun x : ℝ => x * a) hr]
  rw [chirp, hangle, phase_add, phase_int, mul_one, chirp]

theorem chirp_emod {a : ℕ} (ha : 0 < a) (t : ℤ) : chirp a (t % a) = chirp a t := by
  simpa [Int.emod_def, mul_comm] using (chirp_periodic ha).sub_int_mul_eq (x := t) (t / a)

/-- Canceling three chirps gives the unnormalized Fourier entry. -/
theorem chirp_quotient (a : ℕ) (j h : ℤ) :
    chirp a j * chirp a (-h) / chirp a (j - h) = phase ((j : ℝ) * h / a) := by
  simp only [chirp, ← phase_add, ← phase_sub]
  congr 1
  unfold chirpAngle
  push_cast
  by_cases ha : a = 0
  · simp [ha]
  · field_simp
    ring

/-- Unitary Fourier matrix with positive exponential. -/
def normalizedFourier (a : ℕ) : Matrix (Fin a) (Fin a) ℂ :=
  fun j h => (Real.sqrt a : ℂ)⁻¹ * phase ((j.val : ℝ) * h.val / a)

/-- A circulant on the short fiber, indexed by cyclic differences. -/
def chirpCirculant (a : ℕ) : Matrix (Fin a) (Fin a) ℂ :=
  fun j h => (Real.sqrt a : ℂ)⁻¹ * conj (chirp a (((j.val : ℤ) - (h.val : ℤ)) % a))

/-- The circulant and the two outer phase diagonals factor the entire short Fourier matrix. -/
theorem normalizedFourier_factorization {a : ℕ} (ha : 0 < a) :
    normalizedFourier a =
      Matrix.diagonal (fun j : Fin a => chirp a j.val) * chirpCirculant a *
        Matrix.diagonal (fun h : Fin a => chirp a (-(h.val : ℤ))) := by
  ext j h
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [normalizedFourier, chirpCirculant]
  rw [chirp_emod ha]
  change _ = chirp a _ * (_ * conj (phase _)) * chirp a _
  rw [phase_conj]
  have he := chirp_quotient a j.val h.val
  push_cast at he
  rw [← he]
  simp only [chirp, div_eq_mul_inv]
  ring

end

end ShortFourier

end NearSquareRoot
end Computability
end OAI

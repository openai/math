import OAI.Computability.NearSquareRoot.SynchronizedRestoration
import OAI.Computability.NearSquareRoot.SynchronizedComplement
import OAI.Computability.NearSquareRoot.SynchronizedCirculant

/-! # Exact restored circuit from a compressed short transform

The two reflection factors are unitary on all borrowed coordinates. Thus the
amplified operator and its adjoint can be used to extend the local transform by
the identity on the ambient complement.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace SynchronizedRestoration

open Matrix ShortFourier
open scoped Matrix

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

private theorem reflection_unitary (X : Matrix m n ℂ) (hX : Xᴴ * X = 1) :
    (2 : ℝ) • (X * Xᴴ) - 1 ∈ Matrix.unitaryGroup m ℂ := by
  set P := X * Xᴴ
  have hP : Pᴴ = P := by simp [P]
  have hP₂ : P * P = P := by
    dsimp [P]
    rw [Matrix.mul_assoc X, ← Matrix.mul_assoc Xᴴ, hX, Matrix.one_mul]
  apply Matrix.mem_unitaryGroup_iff'.2
  change (((2 : ℝ) • P - 1)ᴴ) * ((2 : ℝ) • P - 1) = 1
  rw [two_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_add, hP, Matrix.conjTranspose_one]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul,
    Matrix.mul_one, hP₂]
  abel

/-- Actual product of the reflections in the compressed subspaces followed by the
original unitary. -/
noncomputable def amplifiedCircuit (E : Matrix m n ℂ) (V : Matrix m m ℂ) (j : ℕ) :
    Matrix m m ℂ :=
  (((2 : ℝ) • (V * (E * Eᴴ) * Vᴴ) - 1) * (1 - (2 : ℝ) • (E * Eᴴ))) ^ j * V

/-- Unitarity on the whole space, including the auxiliary coordinates. -/
theorem amplifiedCircuit_unitary (E : Matrix m n ℂ) (V : Matrix m m ℂ) (j : ℕ)
    (hE : Eᴴ * E = 1) (hV : Vᴴ * V = 1) :
    amplifiedCircuit E V j ∈ Matrix.unitaryGroup m ℂ := by
  have hv : V ∈ Matrix.unitaryGroup m ℂ := Matrix.mem_unitaryGroup_iff'.2 hV
  have hVE : (V * E)ᴴ * (V * E) = 1 := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ, hV, Matrix.one_mul, hE]
  have hfirst := reflection_unitary (V * E) hVE
  rw [Matrix.conjTranspose_mul] at hfirst
  have heq : V * E * (Eᴴ * Vᴴ) = V * (E * Eᴴ) * Vᴴ := by simp [Matrix.mul_assoc]
  rw [heq] at hfirst
  have hsecond : 1 - (2 : ℝ) • (E * Eᴴ) ∈ Matrix.unitaryGroup m ℂ := by
    apply Matrix.mem_unitaryGroup_iff'.2
    change (1 - (2 : ℝ) • (E * Eᴴ))ᴴ * (1 - (2 : ℝ) • (E * Eᴴ)) = 1
    rw [← neg_sub ((2 : ℝ) • (E * Eᴴ)) 1, Matrix.conjTranspose_neg, neg_mul_neg]
    exact Matrix.mem_unitaryGroup_iff'.1 (reflection_unitary E hE)
  exact (Matrix.unitaryGroup m ℂ).mul_mem
    ((Matrix.unitaryGroup m ℂ).pow_mem ((Matrix.unitaryGroup m ℂ).mul_mem hfirst hsecond) j) hv

/-- With the calibrated compression and the three phase diagonals factoring the
short transform, the explicit amplified circuit realizes it and restores all
borrowed coordinates. -/
theorem exact_restored_circuit (E : Matrix m n ℂ) (V : Matrix m m ℂ)
    (U D₁ D₂ D₃ : Matrix n n ℂ) (j : ℕ)
    (hE : Eᴴ * E = 1) (hV : Vᴴ * V = 1) (hU : Uᴴ * U = 1)
    (hc : Eᴴ * V * E = Real.sin (Real.pi / (4 * (j : ℝ) + 2)) • U)
    (hfactor : D₁ * (Uᴴ * D₂ * U) * D₃ = U) :
    extend E D₁ * (amplifiedCircuit E V j)ᴴ * extend E D₂ * amplifiedCircuit E V j *
      extend E D₃ = extend E U := by
  have hU' : U * Uᴴ = 1 := mul_eq_one_comm.mp hU
  apply restore_complement E (amplifiedCircuit E V j) U D₁ D₂ D₃ hE
    (Matrix.mem_unitaryGroup_iff'.1 <| amplifiedCircuit_unitary E V j hE hV) hU'
    (amplify_compression E V U j hE hV hU hU' hc) hfactor

/-- Restore a positive-sign Fourier transform using the three explicit chirp
tables. The only input circuit requirement is a unitary with the stated
calibrated compression to the occupied coordinates. -/
theorem restore_short_fourier {a : ℕ} [NeZero a] (E : Matrix m (Fin a) ℂ)
    (V : Matrix m m ℂ) (j : ℕ) (hE : Eᴴ * E = 1) (hV : Vᴴ * V = 1)
    (hc : Eᴴ * V * E = Real.sin (Real.pi / (4 * (j : ℝ) + 2)) • normalizedFourier a) :
    extend E (diagonal fun t : Fin a => chirp a t.val) * (amplifiedCircuit E V j)ᴴ *
      extend E (diagonal (chirpSpectrum a)) * amplifiedCircuit E V j *
      extend E (diagonal fun t : Fin a => chirp a (-(t.val : ℤ))) =
        extend E (normalizedFourier a) := by
  have hU : (normalizedFourier a)ᴴ * normalizedFourier a = 1 :=
    (normalizedFourier_unitary (a := a)).1
  apply exact_restored_circuit E V _ _ _ _ j hE hV hU hc
  have hd : (normalizedFourier a)ᴴ * diagonal (chirpSpectrum a) * normalizedFourier a =
      chirpCirculant a := by
    rw [← chirp_spectral_diagonal]
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (normalizedFourier a)ᴴ (normalizedFourier a),
      hU, Matrix.one_mul, Matrix.mul_one]
  rw [hd, ← normalizedFourier_factorization (NeZero.pos a)]

end SynchronizedRestoration

end NearSquareRoot
end Computability
end OAI

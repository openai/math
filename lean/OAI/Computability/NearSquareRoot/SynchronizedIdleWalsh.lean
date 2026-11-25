import OAI.Computability.NearSquareRoot.SynchronizedPair
import OAI.Computability.IntegerMultiplication.Fourier.Phase

/-! # Explicit phase table for an idle Walsh pair -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier

open SynchronizedPair Complex

noncomputable section

/-- The six diagonal entries of the three-Walsh factorization of the identity. -/
def identityTable : Fin 6 → ℂ :=
  ![1, -I, (1 + I) * w, (1 - I) * w, 1, -I]

private theorem twice_w_sq : 2 * w ^ 2 = 1 := by
  rw [w, inv_pow, Real.sq_sqrt (by norm_num)]
  norm_num

theorem identityTable_norm (i : Fin 6) : ‖identityTable i‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [Complex.sq_norm, Complex.normSq_apply]
  fin_cases i <;> simp [identityTable, Complex.mul_re, Complex.mul_im] <;>
    nlinarith [twice_w_sq]

theorem identityTable_word : (1 : PairMatrix) =
    walsh * diag (identityTable 0) (identityTable 1) * walsh *
      diag (identityTable 2) (identityTable 3) * walsh *
      diag (identityTable 4) (identityTable 5) := by
  have h : 2 * (w : ℂ) ^ 2 = 1 := by exact_mod_cast twice_w_sq
  have hw : (w : ℂ) ^ 4 = 1 / 4 := by
    linear_combination (2 * (w : ℂ)^2 + 1) / 4 * h
  rw [Matrix.one_fin_two]
  simp only [identityTable, walsh, diag, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp <;> ring_nf <;> norm_num [Complex.I_sq, hw]

/-- Numerators of the six idle-pair phases in eighths of one turn. -/
def identityExponent : Fin 6 → ℤ := ![0, -2, 1, -1, 0, -2]

theorem identityTable_phase (i : Fin 6) :
    identityTable i = IntegerMultiplication.Fourier.phase 8 (identityExponent i) := by
  have angle (n : ℤ) : IntegerMultiplication.Fourier.phase 8 n =
      ((Real.cos (n * Real.pi / 4) : ℝ) : ℂ) +
        ((Real.sin (n * Real.pi / 4) : ℝ) : ℂ) * I := by
    rw [IntegerMultiplication.Fourier.phase, IntegerMultiplication.Fourier.cis,
      show (n : ℝ) / (8 : ℕ) * (2 * Real.pi) = n * Real.pi / 4 by push_cast; ring,
      exp_mul_I, ofReal_sin, ofReal_cos]
  have hw : Real.sqrt 2 / 2 = w := by
    unfold w
    field_simp
    simp
  have hm : IntegerMultiplication.Fourier.phase 8 (-2) = -I := by
    rw [angle, show ((-2 : ℤ) : ℝ) * Real.pi / 4 = -(Real.pi / 2) by push_cast; ring]
    simp
  fin_cases i <;> first
    | exact hm.symm
    | (rw [angle]; norm_num [identityExponent, identityTable, neg_div, Real.cos_pi_div_four,
        Real.sin_pi_div_four, hw] <;> ring)

end

end ShortFourier

end NearSquareRoot
end Computability
end OAI

import OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification.Lower
import OAI.LinearAlgebra.MatrixExponent.Integral.UpperBound

/-!
# Public randomness sufficient for matrix verification

The verifiers are witness-free and work over every infinite field.
These are upper bounds. Optimality among arbitrary branching
arithmetic verifiers with witnesses uses the separately cited
projected-jet theorem.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification

variable (F : Type*) [Field F] [Infinite F]

theorem support_upper {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ' : ρ ≤ 2) :
    Support F ρ (max 2 ((3 / 2 - ρ / 4) ^ 2)) := by
  apply support_of_rectangles hρ hρ'
  have hk : 0 ≤ 1 - ρ / 2 := by linarith
  rw [show 3 / 2 - ρ / 4 = 1 + (1 - ρ / 2) / 2 by ring, ← shape hk (by linarith)]
  exact Integral.arithmetic_upper F hk hk zero_le_one

theorem entropy_upper {η : ℝ} (hη : 0 ≤ η) :
    Entropy F η (max 2 ((3 / 2 - min (3 * η) 2 / 4) ^ 2)) := by
  have h : 0 ≤ min (3 * η) 2 := by positivity
  apply (support_upper F h (min_le_right _ _)).entropy h (by positivity)
  linarith [min_le_left (3 * η) 2]

theorem critical_support : Support F (6 - 4 * Real.sqrt 2) 2 := by
  have hh := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hp := Real.sqrt_nonneg 2
  have h : 6 - 4 * Real.sqrt 2 ≤ 2 := by nlinarith
  simpa only [(support_threshold h).mpr le_rfl] using support_upper F (by nlinarith) h

theorem critical_entropy : Entropy F ((6 - 4 * Real.sqrt 2) / 3) 2 := by
  have hh := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  exact (critical_support F).entropy (by nlinarith) (by norm_num) le_rfl

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification

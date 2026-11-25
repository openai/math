import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI.LinearAlgebra.TensorSpectrum

/-- The error estimate for a normalized finite orbit average. The two boundary
weights and the change in the candidate eigenvalue are charged explicitly. -/
theorem projective_residual_error_bound
    (t u v w q d s r M B η : ℝ)
    (hu : 0 ≤ u ∧ u ≤ B) (hv : 0 ≤ v ∧ v ≤ B) (hw : 0 ≤ w ∧ w ≤ B)
    (hq : 0 ≤ q ∧ q ≤ η) (hd : 0 ≤ d ∧ d ≤ η)
    (hs : 0 ≤ s ∧ s ≤ M) (hr : 0 ≤ r - s ∧ r - s ≤ η)
    (hres : t - s * u = s * (q * v - d * w)) :
    |t - r * u| ≤ (2 * M + 1) * η * B := by
  have hB : 0 ≤ B := hu.1.trans hu.2
  have hη : 0 ≤ η := hq.1.trans hq.2
  have hqv : 0 ≤ q * v := mul_nonneg hq.1 hv.1
  have hdw : 0 ≤ d * w := mul_nonneg hd.1 hw.1
  have hqv_le : q * v ≤ η * B := mul_le_mul hq.2 hv.2 hv.1 hη
  have hdw_le : d * w ≤ η * B := mul_le_mul hd.2 hw.2 hw.1 hη
  have hsqv : s * (q * v) ≤ M * (η * B) :=
    mul_le_mul hs.2 hqv_le hqv (hs.1.trans hs.2)
  have hsdw : s * (d * w) ≤ M * (η * B) :=
    mul_le_mul hs.2 hdw_le hdw (hs.1.trans hs.2)
  have hru : (r - s) * u ≤ η * B := mul_le_mul hr.2 hu.2 hu.1 hη
  have hs_qv : 0 ≤ s * (q * v) := mul_nonneg hs.1 hqv
  have hs_dw : 0 ≤ s * (d * w) := mul_nonneg hs.1 hdw
  have hr_u : 0 ≤ (r - s) * u := mul_nonneg hr.1 hu.1
  have hmain : t - r * u = s * (q * v) - s * (d * w) - (r - s) * u := by
    nlinarith [hres]
  apply abs_le.mpr
  constructor <;> nlinarith

end OAI.LinearAlgebra.TensorSpectrum

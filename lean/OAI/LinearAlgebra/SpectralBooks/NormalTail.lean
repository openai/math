import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Distributions.Gaussian.Real

/-! # Standard normal upper tail -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open MeasureTheory ProbabilityTheory Set

section

/-- The standard normal upper-tail function. -/
noncomputable def normalTail (s : ℝ) : ℝ :=
  (gaussianReal 0 1).real (Ioi s)

theorem normalTail_nonneg (s : ℝ) : 0 ≤ normalTail s := measureReal_nonneg

theorem normalTail_le_one (s : ℝ) : normalTail s ≤ 1 := measureReal_le_one

theorem normalTail_continuous : Continuous normalTail := by
  let : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  change Continuous (fun b : ℝ ↦ (gaussianReal 0 1).real (Ioi b))
  rw [continuous_iff_continuousAt]
  intro s
  have h : IntegrableOn (fun _ : ℝ ↦ (1 : ℝ)) (Ioi (s - 1)) (gaussianReal 0 1) :=
    (integrable_const _).integrableOn
  simpa only [setIntegral_one_eq_measureReal] using
    (h.continuousOn_Ici_primitive_Ioi.continuousAt (Ici_mem_nhds (by linarith : s - 1 < s)))

end

end SpectralBooks
end LinearAlgebra
end OAI

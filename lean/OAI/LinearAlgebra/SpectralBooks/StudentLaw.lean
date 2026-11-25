import OAI.LinearAlgebra.SpectralBooks.StudentQuotient
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-! # Convergence of Student upper tails to the Gaussian upper tail

The denominator of the coupled Student quotient converges almost surely to one
by the strong law for squared normal coordinates. The standard normal law has
no atoms, so its upper tails are limits even when the thresholds vary.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

section

/-- Student laws converge weakly to the standard normal law. -/
theorem studentVariate_tendstoInDistribution :
    TendstoInDistribution studentVariate atTop id (fun _ ↦ gaussianSequence)
      (gaussianReal 0 1) := by
  have h := tendstoInDistribution_of_ae_tendsto (fun d ↦ (measurable_studentVariate d).aemeasurable)
    (measurable_pi_apply 0).aemeasurable studentVariate_tendsto
  refine ⟨h.forall_aemeasurable, measurable_id.aemeasurable, ?_⟩
  have hμ : (⟨gaussianSequence.map (fun x ↦ x 0), inferInstance⟩ : ProbabilityMeasure ℝ) =
      ⟨(gaussianReal 0 1).map id, inferInstance⟩ := by
    ext1
    simpa using gaussianSequence_map_zero
  rw [← hμ]
  exact h.tendsto

/-- Student upper tails converge at moving thresholds to the standard normal upper tail. -/
theorem studentTail_tendsto {s : ℕ → ℝ} {a : ℝ} (hs : Tendsto s atTop (𝓝 a)) :
    Tendsto (fun d ↦ studentTail d (s d)) atTop (𝓝 ((gaussianReal 0 1).real (Ioi a))) := by
  let : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  rw [measureReal_congr (Ioi_ae_eq_Ici (μ := gaussianReal 0 1))]
  apply (studentVariate_tail_tendsto hs).congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with d hd
  exact studentVariate_tail_eq hd (s d)

end

end SpectralBooks
end LinearAlgebra
end OAI

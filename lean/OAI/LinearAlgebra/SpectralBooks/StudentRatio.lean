import OAI.LinearAlgebra.SpectralBooks.GaussianRadiusLaw
import OAI.LinearAlgebra.SpectralBooks.StudentTail

/-! # Student tails as probabilities of Gaussian ratios -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

open MeasureTheory ProbabilityTheory Set

section

/-- The upper tail of the ratio of a standard normal to an independent
normalized Gaussian radius, including the threshold endpoint. -/
theorem gaussianRatio_tail {d : ℕ} (hd : 0 < d) (s : ℝ) :
    ((stdGaussian (EuclideanSpace ℝ (Fin d))).prod (gaussianReal 0 1)).real
      {p | s ≤ Real.sqrt d * p.2 / ‖p.1‖} = studentTail d s := by
  let B : Set (EuclideanSpace ℝ (Fin d) × ℝ) := {p | s ≤ Real.sqrt d * p.2 / ‖p.1‖}
  have hB : MeasurableSet B := measurableSet_le measurable_const (by fun_prop)
  let f (r : ℝ) := (gaussianReal 0 1).real {z | s ≤ Real.sqrt d * z / r}
  have hd' : 0 < Real.sqrt d := by positivity
  let : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  calc
    _ = ∫ x : EuclideanSpace ℝ (Fin d), f ‖x‖ ∂stdGaussian _ := by
      change (((stdGaussian _).prod (gaussianReal 0 1)) B).toReal = _
      rw [Measure.prod_apply hB, ← integral_toReal (measurable_measure_prodMk_left hB).aemeasurable
        (ae_of_all _ fun _ ↦ measure_lt_top _ _)]
      rfl
    _ = ∫ r, chiDensity d r * f r := integral_stdGaussian_norm_eq_chi hd _
    _ = studentTail d s := by
      apply integral_congr_ae
      filter_upwards with r
      by_cases hr : 0 < r
      · have hs : {z : ℝ | s ≤ Real.sqrt d * z / r} = Ici (s / Real.sqrt d * r) := by
          ext z
          simp only [mem_ofPred_eq, mem_Ici, le_div_iff₀ hr]
          rw [div_mul_eq_mul_div, div_le_iff₀ hd', mul_comm _ z]
        dsimp only [f]
        rw [hs]
        exact congrArg (chiDensity d r * ·) (measureReal_congr Ioi_ae_eq_Ici.symm)
      · simp [chiDensity, chiKernel, hr]

end

end

end SpectralBooks
end LinearAlgebra
end OAI

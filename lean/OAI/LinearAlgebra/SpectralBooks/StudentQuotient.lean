import OAI.LinearAlgebra.SpectralBooks.GaussianSquares
import OAI.LinearAlgebra.SpectralBooks.StudentRatio

/-! # The finite-dimensional law of the coupled Student quotient -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open ProbabilityTheory MeasureTheory Filter
open scoped Topology

section

/-- The Gaussian vector forming the denominator of the Student quotient. -/
noncomputable def studentCoordinates (d : ℕ) (x : ℕ → ℝ) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i ↦ x (i.val + 1))

/-- The denominator vector is a standard Gaussian independent of the numerator. -/
theorem studentCoordinates_hasLaw (d : ℕ) :
    HasLaw (fun x ↦ (studentCoordinates d x, x 0))
      ((stdGaussian (EuclideanSpace ℝ (Fin d))).prod (gaussianReal 0 1)) gaussianSequence := by
  have hfin : MeasurePreserving (fun (x : ℕ → ℝ) (i : Fin (d + 1)) ↦ x i)
      gaussianSequence (Measure.pi (fun _ ↦ gaussianReal 0 1)) := by
    refine ⟨by fun_prop, ?_⟩
    rw [gaussianSequence, Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective,
      Measure.infinitePi_eq_pi]
  have heuc : MeasurePreserving (WithLp.toLp 2 : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d))
      (Measure.pi (fun _ ↦ gaussianReal 0 1)) (stdGaussian _) :=
    ⟨by fun_prop, map_pi_eq_stdGaussian⟩
  have hsplit := (measurePreserving_piFinSuccAbove
    (α := fun _ : Fin (d + 1) ↦ ℝ) (fun _ ↦ gaussianReal 0 1) 0).comp hfin
  have hpair := ((heuc.prod (MeasurePreserving.id (gaussianReal 0 1))).comp
      (Measure.measurePreserving_swap.comp hsplit)).hasLaw
  convert hpair using 1
  funext x
  apply Prod.ext
  · ext i
    simp [studentCoordinates, Function.comp_def, MeasurableEquiv.piFinSuccAbove, Fin.tail]
  · rfl

theorem studentVariate_eq_norm (d : ℕ) (x : ℕ → ℝ) :
    studentVariate d x = Real.sqrt d * x 0 / ‖studentCoordinates d x‖ := by
  have hnorm : ‖studentCoordinates d x‖ ^ 2 = ∑ i ∈ Finset.range d, x (i + 1) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, ← Fin.sum_univ_eq_sum_range]
    rfl
  rw [studentVariate, ← hnorm, Real.sqrt_div (sq_nonneg _),
    Real.sqrt_sq (norm_nonneg _), div_div_eq_mul_div, mul_comm]

/-- The upper tail of the coupled quotient agrees exactly with its radial integral. -/
theorem studentVariate_tail_eq {d : ℕ} (hd : 0 < d) (s : ℝ) :
    gaussianSequence.real {x | s ≤ studentVariate d x} = studentTail d s := by
  simp_rw [studentVariate_eq_norm]
  exact ((studentCoordinates_hasLaw d).measureReal_eq
    (p := fun yz ↦ s ≤ Real.sqrt d * yz.2 / ‖yz.1‖)
    (measurableSet_le measurable_const (by fun_prop))).trans (gaussianRatio_tail hd s)

/-- The strict upper tail used in the manuscript has the same value.
Approach the threshold from above and use continuity of the radial tail. -/
theorem studentVariate_strictTail_eq {d : ℕ} (hd : 0 < d) (s : ℝ) :
    gaussianSequence.real {x | s < studentVariate d x} = studentTail d s := by
  let t (n : ℕ) := s + 1 / ((n : ℝ) + 1)
  have ht : Tendsto t atTop (𝓝 s) := by
    simpa [t] using tendsto_one_div_add_atTop_nhds_zero_nat.const_add s
  have hprob : Tendsto (fun n ↦ gaussianSequence {x | t n ≤ studentVariate d x}) atTop
      (𝓝 (gaussianSequence {x | s < studentVariate d x})) := by
    apply tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop
        (measurableSet_lt measurable_const (measurable_studentVariate d))
        (fun _ ↦ measurableSet_le measurable_const (measurable_studentVariate d))
    filter_upwards with x
    by_cases hx : s < studentVariate d x
    · filter_upwards [ht.eventually_lt tendsto_const_nhds hx] with n hn
      exact iff_of_true hn.le hx
    · apply Eventually.of_forall
      intro n
      have hst : s < t n := lt_add_of_pos_right s (by positivity)
      exact iff_of_false (not_le.mpr ((le_of_not_gt hx).trans_lt hst)) hx
  have htail : Tendsto (fun n ↦ gaussianSequence.real {x | t n ≤ studentVariate d x}) atTop
      (𝓝 (studentTail d s)) := by
    simp_rw [studentVariate_tail_eq hd]
    exact (studentTail_continuous hd).continuousAt.tendsto.comp ht
  exact tendsto_nhds_unique ((ENNReal.tendsto_toReal (measure_ne_top _ _)).comp hprob) htail

end

end SpectralBooks
end LinearAlgebra
end OAI

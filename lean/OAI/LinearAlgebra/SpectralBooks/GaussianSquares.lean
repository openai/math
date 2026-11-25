import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.StrongLaw

/-! # Mean square of independent standard Gaussian coordinates -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

section

/-- The law of a countably infinite sequence of independent standard normals. -/
noncomputable def gaussianSequence : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ ↦ gaussianReal 0 1)

instance : IsProbabilityMeasure gaussianSequence := by
  unfold gaussianSequence
  infer_instance

theorem gaussianSequence_map_zero :
    Measure.map (fun x : ℕ → ℝ ↦ x 0) gaussianSequence = gaussianReal 0 1 :=
  Measure.infinitePi_map_eval (fun _ : ℕ ↦ gaussianReal 0 1) 0

/-- The empirical second moment of the coordinates after the zeroth tends to one. -/
theorem gaussianSquares_tendsto :
    ∀ᵐ x ∂gaussianSequence, Tendsto
      (fun d : ℕ ↦ (∑ i ∈ Finset.range d, x (i + 1) ^ 2) / (d : ℝ)) atTop (𝓝 1) := by
  let X (i : ℕ) (x : ℕ → ℝ) := x (i + 1) ^ 2
  have hLaw (i : ℕ) : HasLaw (fun x : ℕ → ℝ ↦ x (i + 1)) (gaussianReal 0 1)
      gaussianSequence :=
    ⟨(measurable_pi_apply (i + 1)).aemeasurable,
      Measure.infinitePi_map_eval (fun _ : ℕ ↦ gaussianReal 0 1) (i + 1)⟩
  have hsq : Integrable (fun x : ℝ ↦ x ^ 2) (gaussianReal 0 1) :=
    integrable_pow_of_mem_interior_integrableExpSet (X := fun x : ℝ ↦ x) (by simp) 2
  have hIndep : iIndepFun (fun (i : ℕ) (x : ℕ → ℝ) ↦ x i ^ 2) gaussianSequence :=
    iIndepFun_infinitePi (X := fun (_ : ℕ) (t : ℝ) ↦ t ^ 2) (by fun_prop)
  have hmean : ∫ x, X 0 x ∂gaussianSequence = 1 := by
    calc
      _ = ∫ t : ℝ, t ^ 2 ∂gaussianReal 0 1 :=
        (hLaw 0).integral_comp (f := fun t : ℝ ↦ t ^ 2) (by fun_prop)
      _ = 1 := by
        have hv := variance_fun_id_gaussianReal (μ := 0) (v := 1)
        rw [variance_eq_integral measurable_id'.aemeasurable] at hv
        simpa using hv
  rw [← hmean]
  exact strong_law_ae_real X ((hLaw 0).integrable_comp hsq)
    (fun i j hij ↦ hIndep.indepFun (Nat.succ_ne_succ_iff.mpr hij))
    (fun i ↦ ((hLaw i).identDistrib (hLaw 0)).comp (u := fun t : ℝ ↦ t ^ 2) (by fun_prop))

/-- The Student variate with `d` degrees of freedom, coupled to its limiting normal
using independent Gaussian coordinates for its denominator. -/
noncomputable def studentVariate (d : ℕ) (x : ℕ → ℝ) : ℝ :=
  x 0 / Real.sqrt ((∑ i ∈ Finset.range d, x (i + 1) ^ 2) / (d : ℝ))

@[fun_prop]
theorem measurable_studentVariate (d : ℕ) : Measurable (studentVariate d) := by
  unfold studentVariate
  fun_prop

/-- Under the Gaussian coupling the Student variates converge almost surely to the numerator. -/
theorem studentVariate_tendsto :
    ∀ᵐ x ∂gaussianSequence, Tendsto (fun d ↦ studentVariate d x) atTop (𝓝 (x 0)) := by
  filter_upwards [gaussianSquares_tendsto] with x hx
  simpa only [studentVariate, Pi.div_def, Real.sqrt_one, div_one] using
    (tendsto_const_nhds (x := x 0)).div hx.sqrt (by simp)

/-- Upper tails of the Student variates converge to the standard Gaussian tail,
including along any sequence of convergent thresholds. -/
theorem studentVariate_tail_tendsto {s : ℕ → ℝ} {a : ℝ} (hs : Tendsto s atTop (𝓝 a)) :
    Tendsto (fun d ↦ gaussianSequence.real {x | s d ≤ studentVariate d x})
      atTop (𝓝 ((gaussianReal 0 1).real (Set.Ici a))) := by
  have hLaw : HasLaw (fun x : ℕ → ℝ ↦ x 0) (gaussianReal 0 1) gaussianSequence :=
    ⟨(measurable_pi_apply 0).aemeasurable, gaussianSequence_map_zero⟩
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  have hne : ∀ᵐ x ∂gaussianSequence, x 0 ≠ a :=
    (hLaw.ae_iff (p := fun t ↦ t ≠ a) (by fun_prop)).mpr ((gaussianReal 0 1).ae_ne a)
  have hlim : Tendsto (fun d ↦ gaussianSequence {x | s d ≤ studentVariate d x})
      atTop (𝓝 (gaussianSequence {x | a ≤ x 0})) := by
    apply tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop
        (measurableSet_le measurable_const (measurable_pi_apply 0))
        (fun d ↦ measurableSet_le measurable_const (measurable_studentVariate d))
    filter_upwards [studentVariate_tendsto, hne] with x hx hxa
    rcases lt_or_gt_of_ne hxa with h | h
    · filter_upwards [hx.eventually_lt hs h] with d hd
      exact iff_of_false (not_le.mpr hd) (not_le.mpr h)
    · filter_upwards [hs.eventually_lt hx h] with d hd
      exact iff_of_true hd.le h.le
  have htail : gaussianSequence.real {x | a ≤ x 0} = (gaussianReal 0 1).real (Set.Ici a) :=
    hLaw.measureReal_eq (p := fun t ↦ a ≤ t) measurableSet_Ici
  rw [← htail]
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp hlim

end

end SpectralBooks
end LinearAlgebra
end OAI

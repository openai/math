import OAI.LinearAlgebra.SpectralBooks.TriangleDensity
import OAI.LinearAlgebra.SpectralBooks.HemisphereMoments
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-! # Hemisphere projections determined by triangle supports -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open MeasureTheory Filter Set
open scoped Topology RealInnerProductSpace
section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
local notation "Sph" => Metric.sphere (0 : E) 1

private theorem integrable_sphere {ρ : Measure Sph} [IsFiniteMeasure ρ]
    {f : Sph → ℝ} (hf : Continuous f) : Integrable f ρ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

private theorem hemisphere_hinge_limit (ρ : Measure Sph) [IsFiniteMeasure ρ] (v w : E) :
    Tendsto (fun a : ℝ => ∫ x : Sph, max (max 0 (a * ⟪(x:E), v⟫)) ⟪(x:E), w⟫ -
      max 0 (a * ⟪(x:E), v⟫) ∂ρ) atTop
      (𝓝 (∫ x in {x : Sph | ⟪(x:E), v⟫ ≤ 0}, max 0 ⟪(x:E), w⟫ ∂ρ)) := by
  let H := {x : Sph | ⟪(x:E), v⟫ ≤ 0}
  have hH : MeasurableSet H := measurableSet_le (by fun_prop) measurable_const
  rw [← integral_indicator hH]
  apply tendsto_integral_filter_of_dominated_convergence (fun x : Sph => |⟪(x:E), w⟫|)
  · exact .of_forall fun a => by fun_prop
  · refine .of_forall fun a => ae_of_all _ fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (le_max_left _ _))]
    calc
      _ ≤ max 0 ⟪(x:E), w⟫ := by grind
      _ ≤ _ := max_le (abs_nonneg _) (le_abs_self _)
  · exact integrable_sphere (by fun_prop)
  · refine ae_of_all _ fun x => ?_
    by_cases hx : ⟪(x:E), v⟫ ≤ 0
    · rw [indicator_of_mem (show x ∈ H from hx)]
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop (0:ℝ)] with a ha
      simp [max_eq_left (mul_nonpos_of_nonneg_of_nonpos ha hx)]
    · rw [indicator_of_notMem (show x ∉ H from hx)]
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop (⟪(x:E), w⟫ / ⟪(x:E), v⟫)] with a ha
      have hle := (div_le_iff₀ (lt_of_not_ge hx)).mp ha
      simp [max_eq_left (hle.trans (le_max_right 0 _))]

private theorem abs_projection_hemisphere_eq {μ ν : Measure Sph}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ v w : E, (∫ x : Sph, max (max 0 ⟪(x:E), v⟫) ⟪(x:E), w⟫ ∂μ) =
      ∫ x : Sph, max (max 0 ⟪(x:E), v⟫) ⟪(x:E), w⟫ ∂ν)
    (v w : E) : (∫ x in {x : Sph | ⟪(x:E), v⟫ ≤ 0}, |⟪(x:E), w⟫| ∂μ) =
      ∫ x in {x : Sph | ⟪(x:E), v⟫ ≤ 0}, |⟪(x:E), w⟫| ∂ν := by
  have hinge (b : E) : (∫ x in {x : Sph | ⟪(x:E), v⟫ ≤ 0}, max 0 ⟪(x:E), b⟫ ∂μ) =
      ∫ x in {x : Sph | ⟪(x:E), v⟫ ≤ 0}, max 0 ⟪(x:E), b⟫ ∂ν := by
    refine tendsto_nhds_unique (hemisphere_hinge_limit μ v b)
      ((hemisphere_hinge_limit ν v b).congr fun a => ?_)
    rw [integral_sub (integrable_sphere (by fun_prop)) (integrable_sphere (by fun_prop)),
      integral_sub (integrable_sphere (by fun_prop)) (integrable_sphere (by fun_prop))]
    have h0 := h (a • v) 0
    simp only [inner_zero_right, max_eq_left (le_max_left _ _), real_inner_smul_right] at h0
    simpa only [real_inner_smul_right, h0] using congrArg
      (· - ∫ x : Sph, max 0 (a * ⟪(x:E), v⟫) ∂ν) (h (a • v) b).symm
  have ha (x : Sph) : |⟪(x:E), w⟫| = max 0 ⟪(x:E), w⟫ + max 0 ⟪(x:E), -w⟫ := by
    rw [inner_neg_right]
    rcases le_total 0 ⟪(x:E), w⟫ with h | h <;> simp [h, neg_nonpos.mpr, neg_nonneg.mpr, abs_of_nonpos, abs_of_nonneg]
  simp_rw [ha]
  rw [integral_add (integrable_sphere (by fun_prop)) (integrable_sphere (by fun_prop)),
      integral_add (integrable_sphere (by fun_prop)) (integrable_sphere (by fun_prop)), hinge, hinge]

/-- Finite triangle integrals determine every even moment of the projections of
each closed hemisphere restriction. -/
theorem hemisphere_moments_eq_of_triangle_integrals {μ ν : Measure Sph}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ v w : E, (∫ x : Sph, max (max 0 ⟪(x:E), v⟫) ⟪(x:E), w⟫ ∂μ) =
      ∫ x : Sph, max (max 0 ⟪(x:E), v⟫) ⟪(x:E), w⟫ ∂ν)
    (z v : E) (j : ℕ) :
    (∫ x in {x : Sph | ⟪(x:E), v⟫ ≤ 0}, ⟪(x:E), z⟫ ^ (2*j) ∂μ) =
    ∫ x in {x : Sph | ⟪(x:E), v⟫ ≤ 0}, ⟪(x:E), z⟫ ^ (2*j) ∂ν := by
  let H := {x : Sph | ⟪(x:E), v⟫ ≤ 0}
  let α := μ.restrict H
  let β := ν.restrict H
  let ρ := α + β
  let : IsFiniteMeasure α := inferInstanceAs (IsFiniteMeasure (μ.restrict H))
  let : IsFiniteMeasure β := inferInstanceAs (IsFiniteMeasure (ν.restrict H))
  let : IsFiniteMeasure ρ := inferInstanceAs (IsFiniteMeasure (α + β))
  let : α.HaveLebesgueDecomposition ρ := Measure.haveLebesgueDecomposition_of_sigmaFinite α ρ
  let : β.HaveLebesgueDecomposition ρ := Measure.haveLebesgueDecomposition_of_sigmaFinite β ρ
  let w (x : Sph) := (α.rnDeriv ρ x).toReal - (β.rnDeriv ρ x).toReal
  have hα : α ≪ ρ := Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)
  have hβ : β ≪ ρ := Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl)
  have hw : Integrable w ρ := by
    have ha := (integrable_toReal_rnDeriv_mul_iff hα).mpr (integrable_const (1:ℝ))
    have hb := (integrable_toReal_rnDeriv_mul_iff hβ).mpr (integrable_const (1:ℝ))
    simpa [w, Pi.sub_def] using ha.sub hb
  have hd {f : Sph → ℝ} (hf : Continuous f) :
      (∫ x, w x * f x ∂ρ) = (∫ x, f x ∂α) - ∫ x, f x ∂β := by
    simp only [w, sub_mul]
    rw [integral_sub ((integrable_toReal_rnDeriv_mul_iff hα).mpr (integrable_sphere hf))
      ((integrable_toReal_rnDeriv_mul_iff hβ).mpr (integrable_sphere hf)),
      integral_toReal_rnDeriv_mul hα, integral_toReal_rnDeriv_mul hβ]
  have he := even_moments_zero_of_abs_projections (u := fun x : Sph => (x:E)) hw
    continuous_subtype_val (fun x => by simp) (fun g => ?_) z j
  · rw [hd (by fun_prop)] at he
    exact sub_eq_zero.mp he
  · rw [hd (by fun_prop)]
    exact sub_eq_zero.mpr (abs_projection_hemisphere_eq h v g)

theorem eq_of_triangle_integrals (μ ν : Measure Sph)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ v w : E, (∫ x : Sph, max (max 0 ⟪(x:E), v⟫) ⟪(x:E), w⟫ ∂μ) =
      ∫ x : Sph, max (max 0 ⟪(x:E), v⟫) ⟪(x:E), w⟫ ∂ν) : μ = ν :=
  sphereMeasure_eq_of_hemisphere_even_moments μ ν (hemisphere_moments_eq_of_triangle_integrals h)

end

end SpectralBooks
end LinearAlgebra
end OAI

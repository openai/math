import OAI.ThreeFlat.PortCut
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace OAI
/-! # Integrating cut inequalities on the graph of ports -/

namespace ThreeFlat

open MeasureTheory Set
open scoped Classical

private noncomputable def level (a : ℝ) : ℝ → ℝ := (Ioc 0 a).indicator 1

private theorem level_integrable (a : ℝ) : Integrable (level a) := by
  apply (integrable_indicator_iff measurableSet_Ioc).2
  exact integrableOn_const measure_Ioc_lt_top.ne

private theorem integral_level {a : ℝ} (ha : 0 ≤ a) : ∫ t, level a t = a := by
  rw [level, integral_indicator_one measurableSet_Ioc, Real.volume_real_Ioc_of_le ha, sub_zero]

private theorem level_mono {a b : ℝ} (hab : a ≤ b) (t : ℝ) : level a t ≤ level b t := by
  by_cases hat : t ∈ Ioc 0 a
  · have hbt : t ∈ Ioc 0 b := ⟨hat.1, hat.2.trans hab⟩
    simp [level, hat, hbt]
  · by_cases hbt : t ∈ Ioc 0 b <;> simp [level, hat, hbt]

private theorem integral_level_variation {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∫ t, |level a t - level b t|) = |a-b| := by
  rcases le_total b a with h | h
  · have hdiff (t : ℝ) : |level a t - level b t| = level a t - level b t :=
      abs_of_nonneg (sub_nonneg.mpr (level_mono h t))
    simp_rw [hdiff]
    rw [integral_sub (level_integrable _) (level_integrable _), integral_level ha,
      integral_level hb, abs_of_nonneg (sub_nonneg.mpr h)]
  · have hdiff (t : ℝ) : |level a t - level b t| = level b t - level a t := by
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (level_mono h t))]
    simp_rw [hdiff]
    rw [integral_sub (level_integrable _) (level_integrable _), integral_level hb,
      integral_level ha, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr h)]

/-- Integrating expansion over the positive superlevel sets of a nonnegative radius
function converts the number of edges across a cut to the total variation on edges. -/
theorem sum_radius_le_edge_variation {V E : Type*} [Fintype V] [Fintype E]
    (l r : E → V) (u : V → ℝ) (hu : ∀ v, 0 ≤ u v) (C : ℝ) (k : ℕ)
    (hsupp : (Finset.univ.filter fun v => 0 < u v).card ≤ k)
    (hexp : ∀ s : Finset V, s.card ≤ k → (s.card : ℝ) ≤ C * cutEdgeCount l r s) :
    ∑ v, u v ≤ C * ∑ e, |u (l e) - u (r e)| := by
  let s (t : ℝ) := Finset.univ.filter fun v => t ∈ Ioc 0 (u v)
  have hsize (t : ℝ) : (s t).card ≤ k := by
    refine (Finset.card_le_card ?_).trans hsupp
    intro v hv
    have hv' : t ∈ Ioc 0 (u v) := (Finset.mem_filter.mp hv).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv'.1.trans_le hv'.2⟩
  have hlevel (t : ℝ) (v : V) : level (u v) t = if v ∈ s t then 1 else 0 := by
    simp [s, level, Set.indicator_apply]
  have point (t : ℝ) :
      (∑ v, level (u v) t) ≤ C * ∑ e, |level (u (l e)) t - level (u (r e)) t| := by
    have hedge (e : E) : |level (u (l e)) t - level (u (r e)) t| =
        if (l e ∈ s t) ≠ (r e ∈ s t) then 1 else 0 := by
      rw [hlevel, hlevel]
      by_cases hl : l e ∈ s t <;> by_cases hr : r e ∈ s t <;> simp [hl, hr]
    simp_rw [hedge, hlevel]
    simpa only [cutEdgeCount, Finset.sum_boole, Finset.filter_mem_eq_inter,
      Finset.univ_inter] using hexp (s t) (hsize t)
  have hvertex (v : V) : Integrable (fun t => level (u v) t) := level_integrable _
  have hedge (e : E) : Integrable (fun t => |level (u (l e)) t - level (u (r e)) t|) :=
    ((level_integrable _).sub (level_integrable _)).abs
  have h := integral_mono
    (integrable_finsetSum Finset.univ (fun v _ => hvertex v))
    ((integrable_finsetSum Finset.univ (fun e _ => hedge e)).const_mul C) point
  rw [integral_finsetSum Finset.univ (fun v _ => hvertex v), integral_const_mul,
    integral_finsetSum Finset.univ (fun e _ => hedge e)] at h
  simpa only [integral_level (hu _), integral_level_variation (hu _) (hu _)] using h

end ThreeFlat

end OAI

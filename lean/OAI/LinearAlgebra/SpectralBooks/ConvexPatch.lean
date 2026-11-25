import Mathlib.Analysis.Convex.Deriv
import Mathlib.Topology.Order.LiminfLimsup

/-! # Recovering a convex dilation profile from its one-sided slopes -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Set Filter
open scoped Topology

private theorem convexPatch_tendsto_increment {f : ℝ → ℝ} {t : ℝ}
    (hconv : ConvexOn ℝ (Icc 0 1) f) (ht : t ∈ Ioo 0 1) :
    Tendsto (fun h ↦ (f (t + h) - f t) / h) (𝓝[>] 0) (𝓝 (derivWithin f (Ioi t) t)) := by
  have hti : t ∈ interior (Icc (0 : ℝ) 1) := by simpa only [interior_Icc] using ht
  have hd := hconv.hasDerivWithinAt_rightDeriv_of_mem_interior hti
  have hshift : Tendsto (fun h : ℝ ↦ t + h) (𝓝[>] 0) (𝓝[>] t) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa using (tendsto_const_nhds (x := t)).add
        (tendsto_id.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0))
    · filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
      exact lt_add_of_pos_right t hh
  simpa only [Function.comp_def, slope_def_field, add_sub_cancel_left] using
    ((hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi).1 hd).comp hshift

/-- The last real-variable step of the flat diagonal law. Here `f t` is the price
of the configuration dilated by `t` and `W` is its normalized mean width. -/
theorem convexPatch_price_eq_of_increment_limsup {f : ℝ → ℝ} {W : ℝ}
    (hconv : ConvexOn ℝ (Icc 0 1) f) (hcont : ContinuousOn f (Icc 0 1)) (hzero : f 0 = 0)
    (htangent : Tendsto (fun h ↦ f h / h) (𝓝[>] 0) (𝓝 W))
    (hinc : ∀ t ∈ Ioo 0 1,
      limsup (fun h ↦ (f (t + h) - f t) / h) (𝓝[>] 0) ≤ W) :
    f 1 = W := by
  have hderiv₀ : HasDerivWithinAt f W (Ioi 0) 0 := by
    apply (hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi).2
    change Tendsto (fun h ↦ slope f 0 h) _ _
    simpa only [slope_def_field, hzero, sub_zero] using htangent
  have hline : EqOn f (fun t ↦ W * t) (Ioo 0 1) := by
    intro t ht
    have hti : t ∈ interior (Icc (0 : ℝ) 1) := by simpa only [interior_Icc] using ht
    have hlim := convexPatch_tendsto_increment hconv ht
    have hupper := hinc t ht
    rw [hlim.limsup_eq] at hupper
    have h₀ : (0 : ℝ) ∈ Icc 0 1 := ⟨le_rfl, zero_le_one⟩
    have hlo := hconv.le_slope_of_hasDerivWithinAt_Ioi h₀ (interior_subset hti) ht.1 hderiv₀
    have hhi := (hconv.slope_le_leftDeriv_of_mem_interior h₀ hti ht.1).trans
      ((hconv.leftDeriv_le_rightDeriv_of_mem_interior hti).trans hupper)
    have heq := le_antisymm hhi hlo
    simp only [slope_def_field, hzero, sub_zero] at heq
    exact (div_eq_iff ht.1.ne').mp heq
  have hclosed := hline.of_subset_closure hcont (continuous_const.mul continuous_id).continuousOn
    Ioo_subset_Icc_self (by rw [closure_Ioo (zero_ne_one : (0 : ℝ) ≠ 1)])
  simpa using hclosed (right_mem_Icc.mpr zero_le_one)

/-- Version of the convex patch argument using an eventual epsilon bound for
each interior difference quotient. -/
theorem convexPatch_price_eq_of_eventually_increment_le {f : ℝ → ℝ} {W : ℝ}
    (hconv : ConvexOn ℝ (Icc 0 1) f) (hcont : ContinuousOn f (Icc 0 1)) (hzero : f 0 = 0)
    (htangent : Tendsto (fun h ↦ f h / h) (𝓝[>] 0) (𝓝 W))
    (hinc : ∀ t ∈ Ioo 0 1, ∀ ε > 0,
      ∀ᶠ h in 𝓝[>] (0 : ℝ), (f (t + h) - f t) / h ≤ W + ε) :
    f 1 = W := by
  apply convexPatch_price_eq_of_increment_limsup hconv hcont hzero htangent
  intro t ht
  have hlim := convexPatch_tendsto_increment hconv ht
  rw [hlim.limsup_eq]
  exact le_of_forall_pos_le_add fun ε hε ↦ le_of_tendsto hlim (hinc t ht ε hε)

end SpectralBooks
end LinearAlgebra
end OAI

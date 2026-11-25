import Mathlib.Analysis.Convex.Deriv

/-! # One-sided tangent prices of convex dilation profiles -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Filter Set
open scoped Topology

/-- At the center of a dilation the price vanishes. Nonnegativity then bounds
its increasing secant slopes from below, giving a finite tangent price. -/
theorem exists_tangentPrice {f : ℝ → ℝ} {R : ℝ} (hR : 0 < R)
    (hconv : ConvexOn ℝ (Icc 0 R) f) (hzero : f 0 = 0)
    (hnonneg : ∀ h ∈ Icc 0 R, 0 ≤ f h) :
    ∃ D : ℝ, 0 ≤ D ∧ Tendsto (fun h ↦ f h / h) (𝓝[>] 0) (𝓝 D) := by
  have hm : MonotoneOn (slope f 0) (Ioo 0 R) :=
    (hconv.monotoneOn_slope_gt ⟨le_rfl, hR.le⟩).mono
      (fun _ hh ↦ ⟨Ioo_subset_Icc_self hh, hh.1⟩)
  have hl : 0 ∈ lowerBounds (slope f 0 '' Ioo 0 R) := by
    rintro _ ⟨h, hh, rfl⟩
    simpa only [slope_def_field, hzero, sub_zero] using
      div_nonneg (hnonneg _ (Ioo_subset_Icc_self hh)) hh.1.le
  have hne : (Ioo 0 R).Nonempty := nonempty_Ioo.mpr hR
  refine ⟨_, le_csInf (hne.image _) hl, ?_⟩
  simpa only [slope_fun_def_field, hzero, sub_zero] using
    hm.tendsto_nhdsWithin_Ioo_right hne ⟨0, hl⟩

/-- Dilating the configuration by a positive factor multiplies its tangent
price by the same factor. -/
theorem tangentPrice_rescale {f : ℝ → ℝ} {D t : ℝ}
    (hf : Tendsto (fun h ↦ f h / h) (𝓝[>] 0) (𝓝 D)) (ht : 0 < t) :
    Tendsto (fun h ↦ f (t * h) / h) (𝓝[>] 0) (𝓝 (t * D)) := by
  have hscale : Tendsto (fun h ↦ t * h) (𝓝[>] 0) (𝓝[>] 0) :=
    tendsto_iff_comap.mpr (comap_mulLeft_nhdsGT_zero ht).ge
  apply ((hf.comp hscale).const_mul t).congr'
  filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
  dsimp
  field_simp

end SpectralBooks
end LinearAlgebra
end OAI

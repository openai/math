import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.InnerProductSpace.Basic

/-! # Approaching a facet through differentiability points

In the proof of the three-page book theorem the inner cube's facet is inside the
larger cube. Rademacher's theorem can thus be applied on a neighborhood on its
outward side.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Filter Set MeasureTheory Module
open scoped Topology InnerProductSpace NNReal

section

/-- A Lipschitz distance function positive at an interior point of the larger
cube has differentiability points tending to that point from the specified side
of a hyperplane. The larger cube can be replaced by any neighborhood of the point. -/
theorem exists_differentiable_seq_above_facet
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {C : Set E} {f : E → ℝ} {K : ℝ≥0} (hf : LipschitzOnWith K f C)
    {p e : E} (hp : p ∈ interior C) (hfp : 0 < f p) (he : ‖e‖ = 1) :
    ∃ y : ℕ → E, Tendsto y atTop (𝓝 p) ∧
      ∀ j, y j ∈ interior C ∧ 0 < ⟪y j - p, e⟫_ℝ ∧
        0 < f (y j) ∧ DifferentiableAt ℝ f (y j) := by
  obtain ⟨g, hg, hfg⟩ := hf.extend_real
  let D := {x : E | DifferentiableAt ℝ g x}
  let _ : MeasurableSpace E := borel E
  have _ : BorelSpace E := ⟨rfl⟩
  have hd : Dense D := Measure.dense_of_ae
    (hg.ae_differentiableAt (μ := (Basis.ofVectorSpace ℝ E).addHaar))
  let H := {x : E | 0 < ⟪x - p, e⟫_ℝ}
  have ho : IsOpen H := isOpen_lt continuous_const
    ((continuous_id.sub continuous_const).inner continuous_const)
  have hc : p ∈ closure H := by
    let ray : ℝ → E := fun t ↦ p + t • e
    have hcont : Continuous ray := continuous_const.add (continuous_id.smul continuous_const)
    have h0 : (0 : ℝ) ∈ closure (Ioi 0) := by simp [closure_Ioi]
    have hr : ray '' Ioi 0 ⊆ H := by
      rintro _ ⟨t, ht, rfl⟩
      simpa [ray, H, real_inner_smul_left, real_inner_self_eq_norm_sq, he] using ht
    have := closure_mono hr (image_closure_subset_closure_image hcont (mem_image_of_mem ray h0))
    simpa [ray] using this
  let U := interior C ∩ {x : E | 0 < g x}
  have hu : IsOpen U := isOpen_interior.inter (isOpen_lt continuous_const hg.continuous)
  have hpu : p ∈ U := ⟨hp, show 0 < g p from hfg (interior_subset hp) ▸ hfp⟩
  have hcl : p ∈ closure ((U ∩ H) ∩ D) :=
    closure_minimal (hd.open_subset_closure_inter (hu.inter ho)) isClosed_closure
      (hu.inter_closure ⟨hpu, hc⟩)
  obtain ⟨y, hy, hlim⟩ := mem_closure_iff_seq_limit.mp hcl
  refine ⟨y, hlim, fun j ↦ ?_⟩
  obtain ⟨⟨⟨hj, hpos⟩, hh⟩, hdiff⟩ := hy j
  refine ⟨hj, hh, (hfg (interior_subset hj)) ▸ hpos, hdiff.congr_of_eventuallyEq ?_⟩
  exact Filter.mem_of_superset (mem_interior_iff_mem_nhds.mp hj) hfg

end

end SpectralBooks
end LinearAlgebra
end OAI

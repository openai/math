import OAI.LinearAlgebra.SpectralBooks.FacetApproach
import Mathlib.Analysis.Convex.Deriv
import Mathlib.LinearAlgebra.AffineSpace.Slope

/-! # A nondegenerate hinge in a non-tripod triangle

On a unit-speed side, the two reverse triangle inequalities give two affine
lower bounds for the distance to the opposite vertex. If both bounds are
strict at an interior point, the secants to the endpoints trap a derivative
strictly between minus one and one. This is the analytic step in the
non-tree-to-plane implication of the row-ordered circuit dichotomy.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Filter Set
open scoped Topology

/-- An interior defect in the tripod distance formula supplies a positive
distance with derivative of absolute value strictly less than one. -/
theorem exists_nonunit_slope {f : ℝ → ℝ} {L t : ℝ}
    (hlip : LipschitzOnWith 1 f (Icc 0 L)) (hcv : ConvexOn ℝ (Icc 0 L) f)
    (ht : t ∈ Ioo 0 L) (htpos : 0 < f t)
    (hleft : f 0 - t < f t) (hright : f L - (L - t) < f t) :
    ∃ y ∈ Ioo 0 L, 0 < f y ∧ DifferentiableAt ℝ f y ∧ |deriv f y| < 1 := by
  have hit : t ∈ interior (Icc 0 L) := by simpa only [interior_Icc] using ht
  obtain ⟨Y, hY, hprop⟩ := exists_differentiable_seq_above_facet hlip hit htpos
    (e := (1 : ℝ)) (by simp)
  have hyin (j : ℕ) : Y j ∈ Ioo 0 L := by simpa only [interior_Icc] using (hprop j).1
  have hcont := hlip.continuousOn.continuousAt (mem_interior_iff_mem_nhds.mp hit)
  have hf := hcont.tendsto.comp hY
  have hl := (tendsto_const_nhds.sub hY).eventually_lt hf hleft
  have hr := (tendsto_const_nhds.sub (tendsto_const_nhds.sub hY)).eventually_lt hf hright
  obtain ⟨j, hjl, hjr⟩ := (hl.and hr).exists
  have hy := hyin j
  have hL := (lt_trans hy.1 hy.2).le
  have hd := (hprop j).2.2.2
  refine ⟨Y j, hy, (hprop j).2.2.1, hd, abs_lt.mpr ⟨?_, ?_⟩⟩
  · apply lt_of_lt_of_le _ (hcv.slope_le_deriv (left_mem_Icc.mpr hL) (show Y j ∈ Icc 0 L from ⟨hy.1.le, hy.2.le⟩)
      hy.1 hd)
    rw [slope_def_field, sub_zero, lt_div_iff₀ hy.1]
    change f 0 - Y j < f (Y j) at hjl
    linarith
  · apply lt_of_le_of_lt (hcv.deriv_le_slope (show Y j ∈ Icc 0 L from ⟨hy.1.le, hy.2.le⟩) (right_mem_Icc.mpr hL)
      hy.2 hd) _
    rw [slope_def_field, div_lt_iff₀ (sub_pos.mpr hy.2)]
    change f L - (L - Y j) < f (Y j) at hjr
    linarith

end SpectralBooks
end LinearAlgebra
end OAI

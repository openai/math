import OAI.LinearAlgebra.FiniteFourier.ForceSupport
import OAI.LinearAlgebra.SpectralBooks.TangentPrice

/-!
# Sublinear prices at the origin of the plane

Joint convexity gives a finite right derivative on every line through the
common origin. The derivatives are positively homogeneous and obey the
same convex interpolation inequalities as the original price.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Filter Set OAI.LinearAlgebra.SpectralBooks
open scoped Topology

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The price in the tangent plane, evaluated on a placement direction. -/
noncomputable def directionalPrice (f : V → ℝ) (x : V) : ℝ :=
  limUnder (𝓝[>] 0) (fun h : ℝ ↦ f (h • x) / h)

variable {f : V → ℝ}

/-- Joint convexity on the whole placement space gives finite right slopes
along every ray at the common origin. -/
theorem tendsto_directionalPrice (hc : ConvexOn ℝ univ f) (hzero : f 0 = 0) (x : V) :
    Tendsto (fun h : ℝ ↦ f (h • x) / h) (𝓝[>] 0) (𝓝 (directionalPrice f x)) := by
  have hline : ConvexOn ℝ univ (fun t : ℝ ↦ f (t • x)) := by
    refine ⟨convex_univ, ?_⟩
    intro u _ v _ a b ha hb hab
    simpa only [smul_eq_mul, add_smul, mul_smul] using
      hc.2 (mem_univ (u • x)) (mem_univ (v • x)) ha hb hab
  have hd := hline.hasDerivWithinAt_sInf_slope_of_mem_interior (x := 0) (by simp)
  apply tendsto_nhds_limUnder
  refine ⟨sInf (slope (fun t : ℝ ↦ f (t • x)) 0 '' {y : ℝ | y ∈ univ ∧ 0 < y}), ?_⟩
  simpa only [slope_fun_def_field, zero_smul, hzero, sub_zero] using
    (hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi).mp hd

/-- A joint convex interpolation inequality passes to the tangent price. -/
theorem convexOn_directionalPrice (hc : ConvexOn ℝ univ f) (hzero : f 0 = 0) :
    ConvexOn ℝ univ (directionalPrice f) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  apply le_of_tendsto_of_tendsto (tendsto_directionalPrice hc hzero _)
    (((tendsto_directionalPrice hc hzero x).const_mul a).add
      ((tendsto_directionalPrice hc hzero y).const_mul b))
  filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
  change f (h • (a • x + b • y)) / h ≤ a * (f (h • x) / h) + b * (f (h • y) / h)
  rw [← mul_div_assoc, ← mul_div_assoc, ← add_div]
  apply div_le_div_of_nonneg_right _ hh.le
  simpa only [smul_add, smul_comm h a, smul_comm h b, smul_eq_mul] using
    hc.2 (mem_univ (h • x)) (mem_univ (h • y)) ha hb hab

/-- The tangent price is positively homogeneous and subadditive on placements. -/
theorem sublinearPrice_directionalPrice (hc : ConvexOn ℝ univ f) (hzero : f 0 = 0) :
    SublinearPrice (directionalPrice f) := by
  have hom (t : ℝ) (ht : 0 ≤ t) (x : V) : directionalPrice f (t • x) = t * directionalPrice f x := by
    rcases ht.eq_or_lt with rfl | hpos
    · simp only [zero_smul, zero_mul]
      apply tendsto_nhds_unique (tendsto_directionalPrice hc hzero _)
      simp [hzero]
    · apply tendsto_nhds_unique (tendsto_directionalPrice hc hzero _)
      simpa only [smul_smul, mul_comm t] using
        tangentPrice_rescale (f := fun h : ℝ ↦ f (h • x)) (tendsto_directionalPrice hc hzero x) hpos
  refine ⟨hom, fun x y ↦ ?_⟩
  have h := (convexOn_directionalPrice hc hzero).2 (mem_univ x) (mem_univ y)
    (show 0 ≤ (1 / 2 : ℝ) by norm_num) (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num)
  rw [← smul_add, hom _ (by norm_num)] at h
  simp only [smul_eq_mul] at h
  linarith

end FiniteFourier
end LinearAlgebra
end OAI

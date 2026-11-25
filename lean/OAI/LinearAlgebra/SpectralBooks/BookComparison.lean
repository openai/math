import OAI.Geometry.HyperbolicGroups.CATZero
import OAI.Geometry.IntegralFillings.Geometry.Comparison

/-! # Equivalent CAT(0) comparisons for the metric ultralimits and the Euclidean pages -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open HyperbolicObstruction SharpIntegralFillings

variable {X : Type*} [MetricSpace X]

/-- Squared-distance convexity along geodesics implies the full comparison
between points on two sides of a triangle. -/
theorem isCAT0_of_catZero (h : CATZero X) : IsCAT0 X := by
  refine ⟨CATZero.segment h, fun x y ↦ ⟨(CATZero.segment_spec h x y).1,
    (CATZero.segment_spec h x y).2.1⟩, fun x y s t hs ht ↦
      (CATZero.segment_spec h x y).2.2 s hs t ht, ?_⟩
  intro o x y s t hs ht
  have h₁ := CATZero.segment_cn h o x (CATZero.segment h o y t) hs
  have h₂ := CATZero.segment_cn h o y x ht
  rw [dist_comm (CATZero.segment h o y t) (CATZero.segment h o x s),
    dist_comm (CATZero.segment h o y t) o, CATZero.segment_left h o y ht,
    dist_comm (CATZero.segment h o y t) x] at h₁
  rw [dist_comm x o] at h₂
  linarith only [h₁, mul_le_mul_of_nonneg_left h₂ hs.1]

/-- The triangle comparison implies the selected geodesic's squared-distance
inequality, by using the endpoint of the second side. -/
theorem catZero_of_isCAT0 (h : IsCAT0 X) : CATZero X := by
  obtain ⟨γ, hend, hdist, hcmp⟩ := h
  intro o x
  refine ⟨γ o x, ⟨(hend o x).1, (hend o x).2, fun s hs t ht ↦ hdist o x s t hs ht⟩, ?_⟩
  intro z t ht
  have h := hcmp o x z t 1 ht (by norm_num)
  rw [(hend o z).2, dist_comm (γ o x t) z, dist_comm o z, dist_comm x z] at h
  linarith only [h]

end SpectralBooks
end LinearAlgebra
end OAI

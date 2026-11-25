import OAI.LinearAlgebra.SpectralBooks.DyadicSegment.GeodesicExtensionGrid
import OAI.LinearAlgebra.SpectralBooks.DyadicSegment.GeodesicExtensionTimes

/-! Exact midpoints generate a constant-speed segment by successive dyadic subdivision. -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Filter Topology DyadicSegment

/-- In a complete metric space, exact midpoints suffice to join every two points by a
constant-speed geodesic. This also applies when more than one midpoint is available. -/
theorem isGeodesic_of_exactMidpoints {X : Type*} [MetricSpace X] [CompleteSpace X]
    (mid : X → X → X)
    (hm : ∀ a b, dist a (mid a b) = dist a b / 2 ∧ dist (mid a b) b = dist a b / 2) :
    HyperbolicObstruction.IsGeodesic X := by
  intro x y
  let : Nonempty X := ⟨x⟩
  let p (t : ℝ) (n : ℕ) := grid mid x y n (index n t)
  let γ (t : ℝ) := limUnder atTop (p t)
  have hlim (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : Tendsto (p t) atTop (𝓝 (γ t)) := by
    apply CauchySeq.tendsto_limUnder
    apply cauchySeq_of_le_geometric_two (C := dist x y)
    intro n
    change dist (grid mid x y n (index n t)) (grid mid x y (n + 1) (index (n + 1) t)) ≤ _
    rw [← grid_even mid x y n (index n t)]
    rcases index_refine n ht.1 with he | ho
    · rw [he, dist_self]
      positivity
    · have h := index_le (n + 1) ht.2
      rw [ho] at h ⊢
      rw [grid_dist mid hm x y (n + 1) _ _ (by omega) h]
      push_cast
      rw [pow_succ]
      apply le_of_eq
      ring
  have hdist {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1)
      (hst : s ≤ t) : dist (γ s) (γ t) = (t - s) * dist x y := by
    apply tendsto_nhds_unique ((hlim s hs).dist (hlim t ht))
    apply (((tendsto_index_div ht.1).sub (tendsto_index_div hs.1)).mul_const (dist x y)).congr'
    apply Eventually.of_forall
    intro n
    dsimp only [p]
    rw [grid_dist mid hm x y n _ _ (index_mono n hst) (index_le n ht.2), sub_div]
  refine ⟨γ, ?_, ?_, ?_⟩
  · apply tendsto_nhds_unique (hlim 0 (by constructor <;> norm_num))
    simp [p, grid_zero]
  · apply tendsto_nhds_unique (hlim 1 (by constructor <;> norm_num))
    simp [p, grid_last]
  · intro s hs t ht
    rcases le_total s t with hst | hts
    · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hst)]
      exact hdist hs ht hst
    · rw [dist_comm, abs_of_nonneg (sub_nonneg.mpr hts)]
      exact hdist ht hs hts

end SpectralBooks
end LinearAlgebra
end OAI

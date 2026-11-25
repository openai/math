import OAI.LinearAlgebra.SpectralBooks.BookFlat
import OAI.LinearAlgebra.SpectralBooks.FlatHullDistance
import OAI.LinearAlgebra.SpectralBooks.FlatHullEmbedding

/-!
# The Euclidean hull of a flat and a tangent point

CAT(0) comparison gives the upper estimate between any two points on the
segments from the apex to the flat. The already determined distances to
the whole flat give the matching lower estimate.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Set SharpIntegralFillings

variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MetricSpace X]

/-- The distances between arbitrary points on two rulings of the tangent hull
agree with the Euclidean model. -/
theorem cat0_segment_pair_dist_sq (hX : IsCAT0 X) {g : E → X} (hg : Isometry g)
    {b P Q : X} {a u v : E} {H s t : ℝ} (hH : 0 ≤ H)
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hb : ∀ w, dist b (g w) ^ 2 = dist a w ^ 2 + H ^ 2)
    (hPb : dist b P = s * dist b (g u)) (hPu : dist (g u) P = (1 - s) * dist b (g u))
    (hQb : dist b Q = t * dist b (g v)) (hQv : dist (g v) Q = (1 - t) * dist b (g v)) :
    dist P Q ^ 2 = dist (AffineMap.lineMap a u s) (AffineMap.lineMap a v t) ^ 2 +
      ((1 - s) * H - (1 - t) * H) ^ 2 := by
  have dP := cat0_segment_dist_flat_sq hX hg hs hb hPb hPu
  have dQ := cat0_segment_dist_flat_sq hX hg ht hb hQb hQv
  apply le_antisymm _ (euclidean_halfSpace_dist_sq_le g
    (mul_nonneg (sub_nonneg.mpr hs.2) hH) (mul_nonneg (sub_nonneg.mpr ht.2) hH) dP dQ)
  obtain ⟨γ, _, hγ⟩ := hX.exists_squared_distance_convex
  have hc := hγ b (g v) P t ht
  rw [cat0_eq_fraction_point hγ ht hQb hQv, dist_comm Q P, hPb, mul_pow, hb u,
    dist_comm (g v) P, dP v, hb v] at hc
  rw [dist_comm (AffineMap.lineMap a u s), euclidean_dist_lineMap_sq _ _ _ ht,
    dist_left_lineMap, Real.norm_of_nonneg hs.1, dist_comm v]
  linarith

/-- A point whose squared distances to an isometrically embedded flat have
the Euclidean formula spans an isometric copy of its entire Euclidean convex
hull with the flat. The embedding extends the given flat and sends the
Euclidean apex to the prescribed point. -/
theorem cat0_flatApexHull_isometry (hX : IsCAT0 X) {g : E → X} (hg : Isometry g)
    (b : X) (a : E) (H : ℝ) (hH : 0 ≤ H)
    (hb : ∀ w, dist b (g w) ^ 2 = dist a w ^ 2 + H ^ 2) :
    ∃ f : flatApexHull a H → X, Isometry f ∧
      (∀ v, f ⟨WithLp.toLp 2 (v, 0), flatApexHull_base_mem a H v⟩ = g v) ∧
      f ⟨WithLp.toLp 2 (a, H), flatApexHull_apex_mem a H⟩ = b := by
  obtain ⟨γ, hends, hd, _⟩ := id hX
  have start (v : E) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
      dist b (γ b (g v) t) = t * dist b (g v) := by
    have h := hd b (g v) 0 t (by simp) ht
    simpa [(hends b (g v)).1, abs_of_nonneg ht.1] using h
  have finish (v : E) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
      dist (g v) (γ b (g v) t) = (1 - t) * dist b (g v) := by
    have h := hd b (g v) 1 t (by simp) ht
    simpa [(hends b (g v)).2, abs_of_nonneg (sub_nonneg.mpr ht.2)] using h
  exact flatApexHull_isometry_of_segments g b a H (fun v t ↦ γ b (g v) t)
    (fun v ↦ (hends b (g v)).1) (fun v ↦ (hends b (g v)).2)
    (fun u v _ _ hs ht ↦ cat0_segment_pair_dist_sq hX hg hH hs ht hb
      (start u hs) (finish u hs) (start v ht) (finish v ht))

end SpectralBooks
end LinearAlgebra
end OAI

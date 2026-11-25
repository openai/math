import Mathlib.Analysis.Convex.Join
import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.Tactic

/-!
# Isometric realization of the hull of a flat and an apex

Every point of the convex hull of the horizontal base and an apex lies on
an apex-to-base segment. The Euclidean pairwise distance formula on these
segments determines an isometric realization of the entire hull.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Set

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MetricSpace X]

/-- The convex hull of the horizontal copy of `E` and the point `(a,H)` in the
Euclidean product of `E` with a line. -/
def flatApexHull (a : E) (H : ℝ) : Set (WithLp 2 (E × ℝ)) :=
  convexHull ℝ (insert (WithLp.toLp 2 (a, H)) (range (fun v : E ↦ WithLp.toLp 2 (v, (0 : ℝ)))))

theorem flatApexHull_base_mem (a : E) (H : ℝ) (v : E) :
    WithLp.toLp 2 (v, (0 : ℝ)) ∈ flatApexHull a H :=
  subset_convexHull _ _ (mem_insert_of_mem _ ⟨v, rfl⟩)

theorem flatApexHull_apex_mem (a : E) (H : ℝ) :
    WithLp.toLp 2 (a, H) ∈ flatApexHull a H :=
  subset_convexHull _ _ (mem_insert _ _)

private theorem horizontal_convex :
    Convex ℝ (range (fun v : E ↦ WithLp.toLp 2 (v, (0 : ℝ)))) := by
  rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩ c d _ _ _
  refine ⟨c • u + d • v, ?_⟩
  apply WithLp.ofLp_injective
  simp

private theorem flatApexHull_segment (a : E) (H : ℝ) (z : flatApexHull a H) :
    ∃ v : E, ∃ t ∈ Icc (0 : ℝ) 1, AffineMap.lineMap (WithLp.toLp 2 (a,H))
      (WithLp.toLp 2 (v, (0 : ℝ))) t = z.val := by
  have hz : z.val ∈ convexHull ℝ (insert (WithLp.toLp 2 (a, H))
      (range (fun v : E ↦ WithLp.toLp 2 (v, (0 : ℝ))))) := z.property
  rw [convexHull_insert (range_nonempty _), horizontal_convex.convexHull_eq,
    mem_convexJoin] at hz
  rcases hz with ⟨_, rfl : _ = _, _, ⟨v, rfl⟩, hz⟩
  rw [segment_eq_image_lineMap] at hz
  exact ⟨v, hz⟩

private theorem model_ruling_dist_sq (a u v : E) (H s t : ℝ) :
    dist (AffineMap.lineMap (WithLp.toLp 2 (a, H)) (WithLp.toLp 2 (u, (0 : ℝ))) s)
      (AffineMap.lineMap (WithLp.toLp 2 (a, H)) (WithLp.toLp 2 (v, (0 : ℝ))) t) ^ 2 =
      dist (AffineMap.lineMap a u s) (AffineMap.lineMap a v t) ^ 2 +
        ((1 - s) * H - (1 - t) * H) ^ 2 := by
  simp only [dist_eq_norm, AffineMap.lineMap_apply_module, WithLp.prod_norm_sq_eq_of_L2]
  simp [Real.norm_eq_abs, sq_abs]

/-- A family of apex-to-base segments satisfying the Euclidean distance formula
induces an isometry of the model convex hull with its prescribed endpoint values. -/
theorem flatApexHull_isometry_of_segments (g : E → X) (b : X) (a : E) (H : ℝ) (P : E → ℝ → X)
    (hzero : ∀ v, P v 0 = b) (hone : ∀ v, P v 1 = g v)
    (hdist : ∀ u v {s t : ℝ}, s ∈ Icc 0 1 → t ∈ Icc 0 1 →
      dist (P u s) (P v t) ^ 2 = dist (AffineMap.lineMap a u s) (AffineMap.lineMap a v t) ^ 2 +
        ((1 - s) * H - (1 - t) * H) ^ 2) :
    ∃ f : flatApexHull a H → X, Isometry f ∧
      (∀ v, f ⟨WithLp.toLp 2 (v, 0), flatApexHull_base_mem a H v⟩ = g v) ∧
      f ⟨WithLp.toLp 2 (a, H), flatApexHull_apex_mem a H⟩ = b := by
  choose foot frac hfrac hrep using flatApexHull_segment a H
  let f (z : flatApexHull a H) := P (foot z) (frac z)
  have metric (u v : E) {s t : ℝ} (hs : s ∈ Icc 0 1) (ht : t ∈ Icc 0 1) :
      dist (P u s) (P v t) =
        dist (AffineMap.lineMap (WithLp.toLp 2 (a,H)) (WithLp.toLp 2 (u, (0 : ℝ))) s)
          (AffineMap.lineMap (WithLp.toLp 2 (a,H)) (WithLp.toLp 2 (v, (0 : ℝ))) t) :=
    (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
      ((hdist u v hs ht).trans (model_ruling_dist_sq a u v H s t).symm)
  refine ⟨f, Isometry.of_dist_eq (fun x y ↦ ?_), ?_, ?_⟩
  · change dist (f x) (f y) = dist x.val y.val
    simpa only [f, hrep] using metric (foot x) (foot y) (hfrac x) (hfrac y)
  · intro v
    let z : flatApexHull a H := ⟨_, flatApexHull_base_mem a H v⟩
    have h := metric (foot z) v (hfrac z) (right_mem_Icc.mpr zero_le_one)
    rw [hrep, AffineMap.lineMap_apply_one, hone] at h
    exact dist_eq_zero.mp (h.trans (dist_self _))
  · let z : flatApexHull a H := ⟨_, flatApexHull_apex_mem a H⟩
    have h := metric (foot z) a (hfrac z) (left_mem_Icc.mpr zero_le_one)
    rw [hrep, AffineMap.lineMap_apply_zero, hzero] at h
    exact dist_eq_zero.mp (h.trans (dist_self _))

end SpectralBooks
end LinearAlgebra
end OAI

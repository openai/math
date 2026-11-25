import OAI.LinearAlgebra.SpectralBooks.BookCAT0
import OAI.LinearAlgebra.SpectralBooks.SquaredDistance

/-!
# Distances to the base of the Euclidean tangent hull

If an apex has the distances of a Euclidean model point to an entire flat in
a CAT(0) space, the same is true along every ruling from the apex to the flat.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Set SharpIntegralFillings
open scoped RealInnerProductSpace

variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MetricSpace X]

/-- The squared distance to a point along an affine segment in a real inner product space. -/
theorem euclidean_dist_lineMap_sq (a v w : E) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    dist (AffineMap.lineMap a v t) w ^ 2 =
      (1 - t) * dist a w ^ 2 + t * dist v w ^ 2 - t * (1 - t) * dist a v ^ 2 := by
  simp only [dist_eq_norm, AffineMap.lineMap_apply_module]
  rw [show (1 - t) • a + t • v - w = (1 - t) • (a - w) + t • (v - w) by module,
    show a - v = (a - w) - (v - w) by abel, norm_add_sq_real, norm_sub_sq_real (a - w),
    norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
    Real.norm_of_nonneg (sub_nonneg.mpr ht.2), Real.norm_of_nonneg ht.1]
  ring

/-- For an isometrically embedded entire flat and an apex with the Euclidean
squared distances to that flat, every point on an apex-to-base segment has the
Euclidean squared distances to the flat. The model apex has foot `a` and altitude `H`. -/
theorem cat0_segment_dist_flat_sq (hX : IsCAT0 X) {g : E → X} (hg : Isometry g)
    {b P : X} {a v : E} {H t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hb : ∀ w, dist b (g w) ^ 2 = dist a w ^ 2 + H ^ 2)
    (hPb : dist b P = t * dist b (g v)) (hPv : dist (g v) P = (1 - t) * dist b (g v))
    (w : E) : dist P (g w) ^ 2 = dist (AffineMap.lineMap a v t) w ^ 2 + ((1 - t) * H) ^ 2 := by
  obtain ⟨γ, _, hγ⟩ := hX.exists_squared_distance_convex
  have hP := cat0_eq_fraction_point hγ ht hPb hPv
  let c := AffineMap.lineMap a v t
  let F := fun z ↦ dist (g z) P ^ 2 - ‖z - c‖ ^ 2
  have major (z : E) : F z ≤ ((1 - t) * H) ^ 2 := by
    have h := hγ b (g v) (g z) t ht
    rw [hP, hb z, hb v, hg.dist_eq] at h
    dsimp only [F, c]
    rw [← dist_eq_norm, dist_comm z, euclidean_dist_lineMap_sq _ _ _ ht, dist_comm (g z) P]
    linarith
  have touch : F v = ((1 - t) * H) ^ 2 := by
    dsimp only [F, c]
    rw [hPv, mul_pow, hb v, ← dist_eq_norm, dist_right_lineMap,
      Real.norm_of_nonneg (sub_nonneg.mpr ht.2)]
    ring
  have hc : ConvexOn ℝ univ F := convexOn_sq_distance_sub_norm_sq
    (cat0_patch_strongConvexOn_dist_sq hX (convex_univ) (fun x _ y _ ↦ hg.dist_eq x y) P) c
  have lower : ((1 - t) * H) ^ 2 ≤ F w := by
    let z := v + (v - w)
    have hm := hc.2 (mem_univ w) (mem_univ z) (show 0 ≤ (1 / 2 : ℝ) by norm_num)
      (show 0 ≤ (1 / 2 : ℝ) by norm_num) (by norm_num)
    have hv : (1 / 2 : ℝ) • w + (1 / 2 : ℝ) • z = v := by dsimp only [z]; module
    rw [hv, touch] at hm
    simp only [smul_eq_mul] at hm
    linarith [major z]
  have heq := le_antisymm (major w) lower
  dsimp only [F, c] at heq
  rw [← dist_eq_norm, dist_comm w, dist_comm (g w) P] at heq
  linarith

end SpectralBooks
end LinearAlgebra
end OAI

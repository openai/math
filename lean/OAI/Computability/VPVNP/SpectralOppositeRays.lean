import OAI.Computability.VPVNP.SpectralTangentRay

/-! # Opposite rays in the spectral tangent space

At a midpoint the rays toward the two original endpoints separate at twice
the speed of either ray. Applying the triangle inequality to points arbitrarily
far along those rays gives the quadratic comparison of Lemma 4.1.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace WireGeometry

open Set

variable {X : Type*} [MetricSpace X] {x y o : X}

/-- Equal-parameter points on the two halves of a segment have exactly the
sum of their distances from the midpoint. -/
theorem opposite_segment_distance (ho : AtFraction x y (1 / 2) o)
    (a : RadialSegment o x) (b : RadialSegment o y) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    dist (a.path t) (b.path t) = 2 * t * dist o x := by
  have hx := ho.1
  rw [dist_comm x o] at hx
  have hxy : dist x y = 2 * dist o x := by linarith only [hx]
  have hy : dist o y = dist o x := by linarith only [ho.2, hx]
  have hxa := a.speed 1 (by simp) t ht
  have hby := b.speed t ht 1 (by simp)
  have hao := a.speed t ht 0 (by simp)
  have hob := b.speed 0 (by simp) t ht
  rw [a.finish, abs_of_nonneg (sub_nonneg.mpr ht.2)] at hxa
  rw [b.finish, hy, abs_of_nonpos (sub_nonpos.mpr ht.2)] at hby
  rw [a.start, sub_zero, abs_of_nonneg ht.1] at hao
  rw [b.start, hy, zero_sub, abs_neg, abs_of_nonneg ht.1] at hob
  have hu := dist_triangle (a.path t) o (b.path t)
  have hl := (dist_triangle x (a.path t) y).trans
    (add_le_add (le_rfl (a := dist x (a.path t))) (dist_triangle (a.path t) (b.path t) y))
  rw [hxa, hby, hxy] at hl
  rw [hao, hob] at hu
  linarith only [hl, hu]

/-- Opposite directions at a midpoint attain the full separation speed. -/
theorem radialSlope_opposite (ho : AtFraction x y (1 / 2) o)
    (a : RadialSegment o x) (b : RadialSegment o y) : radialSlope a b = 2 * dist o x := by
  have hratio (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
      dist (a.path t) (b.path t) / t = 2 * dist o x := by
    rw [opposite_segment_distance ho a b ⟨ht.1.le, ht.2⟩]
    field_simp [ht.1.ne']
  apply le_antisymm
  · exact (radialSlope_le_ratio a b (t := 1) ⟨zero_lt_one, le_rfl⟩).trans_eq
      (hratio 1 ⟨zero_lt_one, le_rfl⟩)
  · apply le_csInf (image_nonempty.mpr (nonempty_Ioc.mpr zero_lt_one))
    rintro _ ⟨t, ht, rfl⟩
    exact (hratio t ht).ge

/-- Opposite rays in the tangent space have linear separation at every
nonnegative parameter, including parameters beyond the original endpoints. -/
theorem tangentRay_opposite (hT : FractionTransport X) (ho : AtFraction x y (1 / 2) o)
    (a : RadialSegment o x) (b : RadialSegment o y) {t : ℝ} (ht : 0 ≤ t) :
    dist (tangentRay a t) (tangentRay b t) = 2 * t * dist o x := by
  rw [tangentRay_cross hT a b ht, radialSlope_opposite ho a b]
  ring

/-- If the two distances to the opposite rays obey the Euclidean quadratic
formula, the triangle inequality at arbitrarily large parameters bounds the
sum of the two squared distances at unit parameter. -/
theorem opposite_ray_quadratic_bound {A B α β : ℝ} (hA : 0 ≤ A) (a b : ℝ → ℝ)
    (htri : ∀ t, 0 ≤ t → 2 * t * A ≤ a t + b t)
    (ha : ∀ t, 0 ≤ t → a t ^ 2 = t ^ 2 * A ^ 2 + B ^ 2 + t * (α ^ 2 - A ^ 2 - B ^ 2))
    (hb : ∀ t, 0 ≤ t → b t ^ 2 = t ^ 2 * A ^ 2 + B ^ 2 + t * (β ^ 2 - A ^ 2 - B ^ 2)) :
    2 * (A ^ 2 + B ^ 2) ≤ α ^ 2 + β ^ 2 := by
  by_contra! h
  let gap := 2 * (A ^ 2 + B ^ 2) - (α ^ 2 + β ^ 2)
  have hgap : 0 < gap := sub_pos.mpr h
  let t := (2 * B ^ 2 + 1) / gap
  have ht : 0 ≤ t := div_nonneg (by positivity) hgap.le
  have hmul : t * gap = 2 * B ^ 2 + 1 := div_mul_cancel₀ _ hgap.ne'
  have hsq := (sq_le_sq₀ (mul_nonneg (mul_nonneg (by norm_num) ht) hA)
    ((mul_nonneg (mul_nonneg (by norm_num) ht) hA).trans (htri t ht))).mpr (htri t ht)
  dsimp only [gap] at hmul
  nlinarith only [hsq, sq_nonneg (a t - b t), ha t ht, hb t ht, hmul]

end WireGeometry

end VPVNP
end Computability
end OAI

import OAI.Geometry.HyperbolicGroups.IndexedFillingValue

/-! # The squared midpoint comparison from tangent sectors

On a Euclidean sector the squared distance from a point of one boundary ray to
a fixed point of the other is a quadratic polynomial. For opposite boundary rays the
triangle inequality forces a sign on the sum of the linear coefficients.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Set HyperbolicObstruction

/-- The boundary distance formula in the Euclidean sector with edge speeds
`A`, `B` and equal-parameter separation speed `c`, including degenerate sectors. -/
def QuadraticRaySectors (X : Type*) [MetricSpace X] : Prop :=
  ∀ (a b : ℝ → X) (A B c : ℝ), a 0 = b 0 →
    (∀ s t : ℝ, 0 ≤ s → 0 ≤ t → dist (a s) (a t) = |s - t| * A) →
    (∀ s t : ℝ, 0 ≤ s → 0 ≤ t → dist (b s) (b t) = |s - t| * B) →
    (∀ t : ℝ, 0 ≤ t → dist (a t) (b t) = t * c) →
    ∀ T : ℝ, 0 < T → dist (a T) (b 1) ^ 2 =
      (T * A) ^ 2 + B ^ 2 + T * (c ^ 2 - A ^ 2 - B ^ 2)

/-- Opposite rays with Euclidean sectors obey squared midpoint comparison at scale one.
Squaring the triangle inequality first gives the sign without an angle or a division
by either of the ray speeds. -/
theorem midpoint_bound_of_opposite_sectors {Y : Type*} [MetricSpace Y]
    (a b : ℝ → Y) (z : Y) (A B c d : ℝ)
    (hab : ∀ T : ℝ, 0 < T → dist (a T) (b T) = 2 * T * A)
    (hac : ∀ T : ℝ, 0 < T → dist (a T) z ^ 2 =
      (T * A) ^ 2 + B ^ 2 + T * (c ^ 2 - A ^ 2 - B ^ 2))
    (hbc : ∀ T : ℝ, 0 < T → dist (b T) z ^ 2 =
      (T * A) ^ 2 + B ^ 2 + T * (d ^ 2 - A ^ 2 - B ^ 2)) :
    2 * A ^ 2 + 2 * B ^ 2 ≤ c ^ 2 + d ^ 2 := by
  by_contra! hfail
  let gap := 2 * A ^ 2 + 2 * B ^ 2 - (c ^ 2 + d ^ 2)
  have hgap : 0 < gap := by dsimp [gap]; linarith
  let T := 1 + 2 * B ^ 2 / gap
  have hT : 0 < T := by dsimp [T]; positivity
  have hlarge : T * gap = gap + 2 * B ^ 2 := by
    dsimp [T]
    rw [add_mul, one_mul, div_mul_cancel₀ _ hgap.ne']
  have htri := dist_triangle (a T) z (b T)
  have hsq := (sq_le_sq₀ (by positivity) (by positivity)).mpr htri
  rw [hab T hT, dist_comm z (b T)] at hsq
  have hs : (2 * T * A) ^ 2 ≤
      2 * (dist (a T) z ^ 2 + dist (b T) z ^ 2) := by
    nlinarith [sq_nonneg (dist (a T) z - dist (b T) z)]
  rw [hac T hT, hbc T hT] at hs
  dsimp only [gap] at hlarge
  nlinarith

variable {X : Type*} [MetricSpace X]

/-- Geodesics from a metric midpoint toward the two endpoints stay opposite. -/
theorem opposite_segment_separation {x y m : X} {a b : ℝ → X}
    (ha : IsSegment a m x) (hb : IsSegment b m y)
    (hm : dist m x + dist m y = dist x y) {s : ℝ} (hs : s ∈ Icc 0 1) :
    dist (a s) (b s) = s * dist x y := by
  have hax := ha.2.2 s hs 1 (by norm_num)
  have hby := hb.2.2 s hs 1 (by norm_num)
  rw [ha.2.1, abs_of_nonpos (sub_nonpos.mpr hs.2)] at hax
  rw [hb.2.1, abs_of_nonpos (sub_nonpos.mpr hs.2)] at hby
  have h := dist_triangle (a s) m (b s)
  rw [dist_comm (a s) m, ha.dist_from_source hs, hb.dist_from_source hs] at h
  have h' := dist_triangle4 x (a s) (b s) y
  rw [dist_comm x (a s), hax, hby] at h'
  rw [← hm]
  nlinarith

end SpectralBooks
end LinearAlgebra
end OAI

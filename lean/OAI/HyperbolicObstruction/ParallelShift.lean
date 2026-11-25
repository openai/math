import OAI.Geometry.HyperbolicGroups.GeometricAction

namespace OAI
/-! # Simultaneous translation of parallel geodesic lines

The distance between synchronously parametrized parallel lines is bounded above.
CAT(0) midpoint comparison forces this distance to be constant for every fixed
relative displacement.
-/

namespace HyperbolicObstruction.CATZero

variable {X : Type*} [MetricSpace X]

private theorem line_mid_reflect (hX : CATZero X) {x : ℝ → X}
    (hx : Isometry x) (r u v : ℝ) :
    x (r + v) = mid hX (x (r + u)) (x (r + (2 * v - u))) := by
  apply eq_segment_of_dist hX (t := 1 / 2) (by norm_num)
  · rw [hx.dist_eq, hx.dist_eq, Real.dist_eq, Real.dist_eq,
      show r + u - (r + v) = u - v by ring,
      show r + u - (r + (2 * v - u)) = 2 * (u - v) by ring, abs_mul]
    norm_num
    ring
  · rw [hx.dist_eq, hx.dist_eq, Real.dist_eq, Real.dist_eq,
      show r + v - (r + (2 * v - u)) = u - v by ring,
      show r + u - (r + (2 * v - u)) = 2 * (u - v) by ring, abs_mul]
    norm_num
    ring

/-- A simultaneous shift preserves every distance between two bounded-distance
oriented unit-speed lines, including distances at unequal parameters. -/
theorem dist_parallel_shift {x y : ℝ → X} (hX : CATZero X)
    (hx : Isometry x) (hy : Isometry y)
    (hxy : ∃ C : ℝ, ∀ u, dist (x u) (y u) ≤ C) (s t h : ℝ) :
    dist (x (s + h)) (y (t + h)) = dist (x s) (y t) := by
  obtain ⟨C, hC⟩ := hxy
  let f (u : ℝ) := dist (x (s + u)) (y (t + u))
  have hb : BddAbove (Set.range f) := by
    refine ⟨|s - t| + C, ?_⟩
    rintro _ ⟨u, rfl⟩
    have htri := dist_triangle (x (s+u)) (x (t+u)) (y (t+u))
    rw [hx.dist_eq, Real.dist_eq, show s + u - (t + u) = s - t by ring] at htri
    exact htri.trans (add_le_add_right (hC (t+u)) _)
  let M := sSup (Set.range f)
  have hle (u : ℝ) : f u ≤ M := le_csSup hb (Set.mem_range_self _)
  have heq (u : ℝ) : f u = M := by
    have hM : M ≤ (f u + M) / 2 := by
      apply csSup_le (Set.range_nonempty f)
      rintro _ ⟨v, rfl⟩
      have hm := dist_mid_mid_le hX (x (s+u)) (x (s+(2*v-u)))
        (y (t+u)) (y (t+(2*v-u)))
      rw [← line_mid_reflect hX hx, ← line_mid_reflect hX hy] at hm
      change f v ≤ (f u + f (2*v-u)) / 2 at hm
      linarith [hle (2*v-u)]
    exact le_antisymm (hle u) (by linarith)
  simpa [f] using (heq h).trans (heq 0).symm

end HyperbolicObstruction.CATZero

end OAI

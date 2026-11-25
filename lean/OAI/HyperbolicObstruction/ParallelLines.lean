import OAI.HyperbolicObstruction.ParallelShift

namespace OAI
/-! # Squared distances between calibrated parallel lines

On two oriented unit-speed lines, a common 1-Lipschitz coordinate bounds the
squared horizontal displacement by the squared ambient distance. The CAT(0)
quadrilateral inequality makes the difference midpoint-concave, hence constant
on the entire line. This yields the Euclidean product formula between the lines.
-/

namespace HyperbolicObstruction.CATZero

variable {X : Type*} [MetricSpace X]

private theorem eq_of_bddBelow_midpointConcave {f : ℝ → ℝ}
    (hb : BddBelow (Set.range f))
    (hm : ∀ u h : ℝ, f (u - h) + f (u + h) ≤ 2 * f u) (s t : ℝ) :
    f s = f t := by
  have hmin (v : ℝ) : f v = ⨅ z, f z := by
    refine le_antisymm ?_ (ciInf_le hb v)
    have hi : (f v + ⨅ z, f z) / 2 ≤ ⨅ z, f z := by
      apply le_ciInf
      intro u
      have href := hm u (u - v)
      rw [show u - (u - v) = v by ring] at href
      linarith [ciInf_le hb (u + (u - v))]
    linarith
  exact (hmin s).trans (hmin t).symm

/-- Parallel oriented lines with a common real calibration split into the
squared distance between their zero-phase points and the squared phase difference. -/
theorem dist_sq_parallel_lines {x y : ℝ → X} (hX : CATZero X)
    (hx : Isometry x) (hy : Isometry y)
    (hxy : ∃ C : ℝ, ∀ u, dist (x u) (y u) ≤ C)
    {b : X → ℝ} (hb : LipschitzWith 1 b) {bx by' : ℝ}
    (hbx : ∀ s, b (x s) = s + bx) (hby : ∀ t, b (y t) = t + by') (s t : ℝ) :
    dist (x s) (y t) ^ 2 =
      dist (x (-bx)) (y (-by')) ^ 2 + (s + bx - (t + by')) ^ 2 := by
  have shift (s t : ℝ) : dist (x s) (y t) = dist (x (s - t)) (y 0) := by
    simpa using dist_parallel_shift hX hx hy hxy (s - t) 0 t
  let f (u : ℝ) := dist (x u) (y 0) ^ 2 - (u + bx - by') ^ 2
  have hbdd : BddBelow (Set.range f) := by
    refine ⟨0, fun z hz => ?_⟩
    obtain ⟨u, rfl⟩ := hz
    have h : |u + bx - by'| ≤ dist (x u) (y 0) := by
      simpa only [Real.dist_eq, hbx, hby, zero_add, NNReal.coe_one, one_mul] using
        hb.dist_le_mul (x u) (y 0)
    have hsq := pow_le_pow_left₀ (abs_nonneg _) h 2
    simpa only [f, sq_abs] using sub_nonneg.mpr hsq
  have hconcave (u h : ℝ) : f (u - h) + f (u + h) ≤ 2 * f u := by
    have hq := quadrilateral hX (x u) (x (u+h)) (y h) (y 0)
    rw [shift u h, shift (u+h) h, show u + h - h = u by ring, dist_comm (y 0) (x u),
      hx.dist_eq, hy.dist_eq, Real.dist_eq, Real.dist_eq, sq_abs, sq_abs] at hq
    dsimp only [f]
    nlinarith [sq_nonneg (dist (mid hX (x u) (y h)) (mid hX (x (u + h)) (y 0)))]
  have he := eq_of_bddBelow_midpointConcave hbdd hconcave (s-t) (-bx - -by')
  rw [shift s t, shift (-bx) (-by')]
  dsimp only [f] at he
  nlinarith

end HyperbolicObstruction.CATZero

end OAI

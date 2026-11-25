import OAI.LinearAlgebra.SpectralBooks.CurvatureBlowup.BlowupGeodesic
import OAI.LinearAlgebra.SpectralBooks.Comparison

/-! # Midpoint comparison in a spectral geodesic space

The blow-up at a midpoint supplies opposite rays and a third ray. The quadratic
distance law on its two sectors gives the midpoint inequality. At equality the
two original equal-parameter separation ratios already attained their infima.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open HyperbolicObstruction Set CurvatureBlowup

variable {X : Type*} [MetricSpace X]

/-- The midpoint estimate and its equality case for three segments out of a
midpoint, using the quadratic sector law in its pointed blow-up. -/
theorem midpoint_comparison_of_quadratic_blowup
    (hB : RadialBusemann X) {m x y z : X} (hsec : QuadraticRaySectors (Space m))
    {a b w : ℝ → X} (ha : IsSegment a m x) (hb : IsSegment b m y) (hw : IsSegment w m z)
    (hmx : dist m x = dist x y / 2) (hmy : dist m y = dist x y / 2) :
    2 * dist z m ^ 2 + dist x y ^ 2 / 2 ≤ dist z x ^ 2 + dist z y ^ 2 ∧
    (2 * dist z m ^ 2 + dist x y ^ 2 / 2 = dist z x ^ 2 + dist z y ^ 2 →
      ∀ s ∈ Icc (0 : ℝ) 1,
        dist (a s) (w s) = s * dist x z ∧ dist (b s) (w s) = s * dist y z) := by
  obtain ⟨c, hc, hcx, hcr, hcw⟩ := dist_pair hB ha hw
  obtain ⟨d, hd, hdy, hdr, hdw⟩ := dist_pair hB hb hw
  have hop (T : ℝ) (hT : 0 < T) : dist (ray ha T) (ray hb T) = 2 * T * dist m x := by
    rw [dist_opposite ha hb (fun _ hs ↦ opposite_segment_separation ha hb (by linarith) hs) hT.le]
    rw [hmx]
    ring
  have poly {p : X} {r : ℝ → X} (hr : IsSegment r m p) {e : ℝ}
      (he : ∀ t, 0 ≤ t → dist (ray hr t) (ray hw t) = t * e) :=
    hsec (ray hr) (ray hw) (dist m p) (dist m z) e (ray_zero hr hw)
      (fun _ _ hs ht ↦ dist_same hr hs ht) (fun _ _ hs ht ↦ dist_same hw hs ht) he
  have hbpoly := poly hb hdw
  rw [show dist m y = dist m x by linarith] at hbpoly
  have hmid := midpoint_bound_of_opposite_sectors (ray ha) (ray hb) (ray hw 1)
    (dist m x) (dist m z) c d hop (poly ha hcw) hbpoly
  rw [hmx] at hmid
  rw [dist_comm z m, dist_comm z x, dist_comm z y]
  have hc₂ := (sq_le_sq₀ hc dist_nonneg).mpr hcx
  have hd₂ := (sq_le_sq₀ hd dist_nonneg).mpr hdy
  refine ⟨by linarith, ?_⟩
  intro heq s hs
  have hceq : c = dist x z := by nlinarith
  have hdeq : d = dist y z := by nlinarith
  subst c d
  rcases eq_or_lt_of_le hs.1 with rfl | hspos
  · simp [ha.1, hb.1, hw.1]
  · exact ⟨le_antisymm (hB m x z a w ha hw s hs)
        (by simpa [mul_comm] using (le_div_iff₀ hspos).mp (hcr s ⟨hspos, hs.2⟩)),
      le_antisymm (hB m y z b w hb hw s hs)
        (by simpa [mul_comm] using (le_div_iff₀ hspos).mp (hdr s ⟨hspos, hs.2⟩))⟩

/-- Quadratic sectors at every tangent midpoint give the CAT(0) inequality
on every whole geodesic segment. -/
theorem catZero_of_quadratic_blowups (g : IsGeodesic X) (hB : RadialBusemann X)
    (hsec : ∀ o : X, QuadraticRaySectors (Space o)) : CATZero X := by
  apply catZero_of_segment_midpoint g
  intro γ x y hγ z
  let m := γ (1 / 2)
  have ht : (1 / 2 : ℝ) ∈ Icc 0 1 := by norm_num
  have hmx : dist m x = dist x y / 2 := by
    rw [dist_comm]
    simpa [m, div_eq_mul_inv, mul_comm] using hγ.dist_from_source ht
  have hmy : dist m y = dist x y / 2 := by
    have h := hγ.2.2 _ ht 1 (by norm_num)
    rw [hγ.2.1] at h
    norm_num at h
    simpa [m, div_eq_mul_inv, mul_comm] using h
  obtain ⟨a, ha⟩ := g m x
  obtain ⟨b, hb⟩ := g m y
  obtain ⟨w, hw⟩ := g m z
  have h := (midpoint_comparison_of_quadratic_blowup hB (hsec m) ha hb hw hmx hmy).1
  change dist z m ^ 2 ≤ _
  linarith

end SpectralBooks
end LinearAlgebra
end OAI

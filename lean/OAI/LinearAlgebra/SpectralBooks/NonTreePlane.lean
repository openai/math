import OAI.LinearAlgebra.SpectralBooks.NonTripodSlope
import OAI.LinearAlgebra.SpectralBooks.PricePlanePatch

/-! # A four-point violation yields a spectral Euclidean plane

This is the non-tree implication of the spectral geometry theorem used in both
manuscripts. The ambient space carries the tensor prices and satisfies the
CAT(0) comparison condition. A four-point violation gives an interval on
which distance to an off-segment point has an interior derivative of norm
strictly below one. Its tangent hull contains an open Euclidean disk.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Filter Set HyperbolicObstruction
open scoped Topology

variable {F X : Type*} [Field F] [MetricSpace X] (P : SpectralPlacementPrices F X) (hX : CATZero X)

include P hX

private theorem plane_of_side_defect {L t : ℝ} {c : ℝ → X} {z : X}
    (hc : ∀ s ∈ Icc 0 L, ∀ u ∈ Icc 0 L, dist (c s) (c u) = dist s u)
    (ht : t ∈ Ioo 0 L) (hpos : 0 < dist (c t) z)
    (hl : dist (c 0) z - t < dist (c t) z)
    (hr : dist (c L) z - (L-t) < dist (c t) z) :
    Nonempty (SpectralPlacementPrices F (EuclideanSpace ℝ (Fin 2))) := by
  let f (s : ℝ) := dist (c s) z
  have hLip : LipschitzOnWith 1 f (Icc 0 L) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul, ← hc x hx y hy] using
      abs_dist_sub_le (c x) (c y) z
  have hcv := cat0_patch_convexOn_dist (isCAT0_of_catZero hX) (convex_Icc 0 L) hc z
  obtain ⟨y, hy, hfy, hdiff, hsmall⟩ := exists_nonunit_slope hLip hcv ht hpos hl hr
  let ω := Ultrafilter.of (atTop : Filter ℕ)
  let s (n : ℕ) : ℝ := 1 / (n+1)
  have hs (n : ℕ) : 0 < s n := by dsimp [s]; positivity
  have hU : Icc 0 L ∈ 𝓝 y := Icc_mem_nhds hy.1 hy.2
  obtain ⟨_, Q, _⟩ := Book.exists_tangentHull_spectralPrices ω hs hc hU hX z
    (M := 1) zero_le_one (Ultrafilter.of_le _)
    tendsto_one_div_add_atTop_nhds_zero_nat P hdiff.hasDerivAt.hasGradientAt'
  apply Nonempty.intro (Q.planeOfFlatApexHull ?_)
  change 0 < (1 : ℝ) * (f y * Real.sqrt (1 - ‖deriv f y‖ ^ 2))
  rw [one_mul]
  apply mul_pos hfy (Real.sqrt_pos.mpr ?_)
  rw [Real.norm_eq_abs]
  nlinarith [sq_nonneg (deriv f y), abs_nonneg (deriv f y),
    mul_pos (sub_pos.mpr hsmall) (show 0 < 1 + |deriv f y| by positivity)]

/-- Price-preserving CAT(0) realization of a strict four-point violation
suffices to produce a spectral plane over the same field. -/
theorem spectralPlane_of_fourPointDefect (a b z w : X)
    (hbad : max (dist a z + dist b w) (dist a w + dist b z) < dist a b + dist z w) :
    Nonempty (SpectralPlacementPrices F (EuclideanSpace ℝ (Fin 2))) := by
  let L := dist a b
  have hL : 0 < L := by
    apply dist_pos.mpr
    rintro rfl
    rw [dist_self, zero_add, max_lt_iff] at hbad
    linarith [dist_triangle_left z w a]
  let c (t : ℝ) := CATZero.segment hX a b (t/L)
  have hfrac {t : ℝ} (ht : t ∈ Icc 0 L) : t/L ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg ht.1 hL.le, (div_le_one hL).mpr ht.2⟩
  have hc (s : ℝ) (hs : s ∈ Icc 0 L) (u : ℝ) (hu : u ∈ Icc 0 L) :
      dist (c s) (c u) = dist s u := by
    dsimp only [c]
    rw [CATZero.segment_dist hX a b (hfrac hs) (hfrac hu)]
    change |s/L - u/L| * L = _
    rw [← sub_div, abs_div, abs_of_pos hL, div_mul_cancel₀ _ hL.ne', Real.dist_eq]
  have hc0 : c 0 = a := by simp [c, (CATZero.segment_spec hX a b).1]
  have hcL : c L = b := by simp [c, hL.ne', (CATZero.segment_spec hX a b).2.1]
  let t (x : X) := (dist a x - dist b x + L)/2
  let h (x : X) := (dist a x + dist b x - L)/2
  have ht (x : X) : t x ∈ Icc 0 L := by
    dsimp [t,L]
    constructor <;> linarith [dist_triangle_left b x a, dist_triangle a b x, dist_comm b a]
  have hh (x : X) : 0 ≤ h x := by
    dsimp [h,L]
    linarith [dist_triangle_right a b x]
  have deficient : h z < dist (c (t z)) z ∨ h w < dist (c (t w)) w := by
    by_contra! hneg
    have tri := dist_triangle z (c (t z)) w
    have tri' := dist_triangle (c (t z)) (c (t w)) w
    rw [dist_comm z (c (t z))] at tri
    rw [hc _ (ht z) _ (ht w), Real.dist_eq] at tri'
    rw [max_lt_iff] at hbad
    cases le_total (t z) (t w) with
    | inl hz =>
      rw [abs_of_nonpos (sub_nonpos.mpr hz)] at tri'
      dsimp [h,t,L] at hneg tri'
      linarith [hneg.1,hneg.2,hbad.1,hbad.2]
    | inr hw =>
      rw [abs_of_nonneg (sub_nonneg.mpr hw)] at tri'
      dsimp [h,t,L] at hneg tri'
      linarith [hneg.1,hneg.2,hbad.1,hbad.2]
  have directly (x : X) (hd : h x < dist (c (t x)) x) :
      Nonempty (SpectralPlacementPrices F (EuclideanSpace ℝ (Fin 2))) := by
    have hl : dist a x - t x = h x := by dsimp [t,h]; ring
    have hr : dist b x - (L - t x) = h x := by dsimp [t,h]; ring
    have hit : t x ∈ Ioo 0 L := by
      constructor
      · apply lt_of_le_of_ne (ht x).1
        intro eq
        rw [← eq, hc0] at hd
        linarith [hl]
      · apply lt_of_le_of_ne (ht x).2
        intro eq
        rw [eq, hcL] at hd
        linarith [hr]
    exact plane_of_side_defect P hX hc hit ((hh x).trans_lt hd)
      (by rwa [hc0,hl]) (by rwa [hcL,hr])
  exact deficient.elim (directly z) (directly w)

end SpectralBooks
end LinearAlgebra
end OAI

import OAI.LinearAlgebra.SpectralBooks.NonTripodSlope
import OAI.LinearAlgebra.SpectralBooks.BookCAT0
import OAI.LinearAlgebra.SpectralBooks.BookComparison

namespace OAI
/-! # A transverse geodesic with a non-unit slope

In a CAT(0) space, a strict four-point defect forces a point strictly above the
tripod comparison along one side. Distance to that point has a derivative of
absolute value strictly below one somewhere in the interior of the side.
-/

namespace ThreeFlat

open Set HyperbolicObstruction LinearAlgebra.SpectralBooks

/-- An interior differentiability point on a geodesic witnessing transverse spread. -/
theorem exists_segment_nonunit_slope_of_fourPointDefect {Y : Type*} [MetricSpace Y]
    (hY : CATZero Y) (a b z w : Y)
    (hbad : max (dist a z + dist b w) (dist a w + dist b z) < dist a b + dist z w) :
    ∃ (L : ℝ) (c : ℝ → Y) (p : Y) (y : ℝ),
      (∀ s ∈ Icc 0 L, ∀ u ∈ Icc 0 L, dist (c s) (c u) = dist s u) ∧
      y ∈ Ioo 0 L ∧ 0 < dist (c y) p ∧
      DifferentiableAt ℝ (fun u ↦ dist (c u) p) y ∧
      |deriv (fun u ↦ dist (c u) p) y| < 1 := by
  let L := dist a b
  have hL : 0 < L := by
    apply dist_pos.mpr
    rintro rfl
    rw [dist_self, zero_add, max_lt_iff] at hbad
    linarith [dist_triangle_left z w a]
  let c (t : ℝ) := CATZero.segment hY a b (t/L)
  have hfrac {t : ℝ} (ht : t ∈ Icc 0 L) : t/L ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg ht.1 hL.le, (div_le_one hL).mpr ht.2⟩
  have hc (s : ℝ) (hs : s ∈ Icc 0 L) (u : ℝ) (hu : u ∈ Icc 0 L) :
      dist (c s) (c u) = dist s u := by
    dsimp only [c]
    rw [(CATZero.segment_spec hY a b).2.2 _ (hfrac hs) _ (hfrac hu)]
    change |s/L - u/L| * L = _
    rw [← sub_div, abs_div, abs_of_pos hL, div_mul_cancel₀ _ hL.ne', Real.dist_eq]
  have hc0 : c 0 = a := by simp [c, (CATZero.segment_spec hY a b).1]
  have hcL : c L = b := by simp [c, hL.ne', (CATZero.segment_spec hY a b).2.1]
  let t (x : Y) := (dist a x - dist b x + L)/2
  let h (x : Y) := (dist a x + dist b x - L)/2
  have ht (x : Y) : t x ∈ Icc 0 L := by
    dsimp [t,L]
    constructor <;> linarith [dist_triangle_left b x a, dist_triangle a b x, dist_comm b a]
  have hh (x : Y) : 0 ≤ h x := by
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
  obtain ⟨p, hd⟩ : ∃ p : Y, h p < dist (c (t p)) p :=
    deficient.elim (fun hz ↦ ⟨z, hz⟩) (fun hw ↦ ⟨w, hw⟩)
  have hl : dist a p - t p = h p := by dsimp [t,h]; ring
  have hr : dist b p - (L - t p) = h p := by dsimp [t,h]; ring
  have hit : t p ∈ Ioo 0 L := by
    constructor
    · apply lt_of_le_of_ne (ht p).1
      intro eq
      rw [← eq, hc0] at hd
      linarith [hl]
    · apply lt_of_le_of_ne (ht p).2
      intro eq
      rw [eq, hcL] at hd
      linarith [hr]
  let f (s : ℝ) := dist (c s) p
  have hLip : LipschitzOnWith 1 f (Icc 0 L) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul, ← hc x hx y hy] using
      abs_dist_sub_le (c x) (c y) p
  have hcv := cat0_patch_convexOn_dist (isCAT0_of_catZero hY) (convex_Icc 0 L) hc p
  obtain ⟨y, hy, hfy, hdiff, hsmall⟩ := exists_nonunit_slope hLip hcv hit
    ((hh p).trans_lt hd) (by change dist (c 0) p - t p < dist (c (t p)) p; rwa [hc0, hl])
    (by change dist (c L) p - (L - t p) < dist (c (t p)) p; rwa [hcL, hr])
  exact ⟨L, c, p, y, hc, hy, hfy, hdiff, hsmall⟩

end ThreeFlat

end OAI

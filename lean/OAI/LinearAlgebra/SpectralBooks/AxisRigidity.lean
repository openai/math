import OAI.Geometry.HyperbolicGroups.CATZero

/-!
# Rigidity of the marked axes

In the normalized configuration of Lemma `axis-rigidity`, contraction of the
marked radii and equality in the sum of diameters force equality on every
radius. CAT(0) comparison then recovers the Euclidean metric between all the
points on different marked axes, including the interiors of the segments.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open HyperbolicObstruction

variable {X : Type*} [MetricSpace X] {D : ℕ}

/-- Saturation of the total diameter forces every diameter and radius to
attain its Euclidean length. The two Boolean values index opposite signs. -/
theorem axis_diameters_and_radii_of_sum (o : X) (x : Fin D → Bool → X)
    {r : ℝ} (hr : ∀ i b, dist o (x i b) ≤ r)
    (hsum : ∑ i, dist (x i false) (x i true) = 2 * r * D) :
    (∀ i, dist (x i false) (x i true) = 2 * r) ∧
      (∀ i b, dist o (x i b) = r) := by
  have htri (i : Fin D) :
      dist (x i false) (x i true) ≤ dist o (x i false) + dist o (x i true) := by
    simpa only [dist_comm (x i false) o] using dist_triangle (x i false) o (x i true)
  have hdiam (i : Fin D) : dist (x i false) (x i true) ≤ 2 * r := by
    linarith [htri i, hr i false, hr i true]
  have hsum' : ∑ i, dist (x i false) (x i true) = ∑ _ : Fin D, (2 * r : ℝ) := by
    simpa [mul_comm] using hsum
  have heq (i : Fin D) : dist (x i false) (x i true) = 2 * r :=
    (Finset.sum_eq_sum_iff_of_le (fun k _ => hdiam k)).mp hsum' i (Finset.mem_univ i)
  refine ⟨heq, ?_⟩
  intro i b
  cases b <;> linarith [heq i, htri i, hr i false, hr i true]

/-- The unit-normalized form of diameter saturation. -/
theorem axis_diameters_and_radii (o : X) (x : Fin D → Bool → X)
    (hr : ∀ i b, dist o (x i b) ≤ 1)
    (hsum : ∑ i, dist (x i false) (x i true) = 2 * D) :
    (∀ i, dist (x i false) (x i true) = 2) ∧ (∀ i b, dist o (x i b) = 1) := by
  simpa using axis_diameters_and_radii_of_sum o x hr (by simpa using hsum)

/-- Arclength parametrization of a marked unit diameter on `[-1,1]`, from
the negative endpoint to the positive endpoint. -/
noncomputable def axisSegment (h : CATZero X) (a b : X) (s : ℝ) : X :=
  CATZero.segment h a b ((s + 1) / 2)

private theorem axis_parameter {s : ℝ} (hs : s ∈ Set.Icc (-1 : ℝ) 1) :
    (s + 1) / 2 ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨by linarith [hs.1], by linarith [hs.2]⟩

theorem dist_axisSegment (h : CATZero X) {a b : X} (hab : dist a b = 2)
    {s t : ℝ} (hs : s ∈ Set.Icc (-1 : ℝ) 1) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    dist (axisSegment h a b s) (axisSegment h a b t) = |s - t| := by
  rw [axisSegment, axisSegment, (CATZero.segment_spec h a b).2.2 _ (axis_parameter hs) _
    (axis_parameter ht), hab, ← sub_div, add_sub_add_right_eq_sub, abs_div]
  norm_num

theorem axis_origin_eq_mid (h : CATZero X) {o a b : X} (hab : dist a b = 2)
    (ha : dist o a = 1) (hb : dist o b = 1) : o = CATZero.mid h a b := by
  apply CATZero.eq_segment_of_dist h (t := 1/2) (by norm_num)
  · rw [dist_comm, ha, hab]
    norm_num
  · rw [hb, hab]
    norm_num

theorem axisSegment_zero (h : CATZero X) {o a b : X} (hab : dist a b = 2)
    (ha : dist o a = 1) (hb : dist o b = 1) : axisSegment h a b 0 = o := by
  simpa only [axisSegment, zero_add, CATZero.mid] using (axis_origin_eq_mid h hab ha hb).symm

/-- CAT(0) comparison on both halves of a marked diameter. If the squared
distances to its endpoints are bounded by the Euclidean perpendicular
values, every point on the diameter has that perpendicular distance. -/
theorem axis_perpendicular_distance (h : CATZero X) {o a b : X} (z : X)
    (hab : dist a b = 2) (ha : dist o a = 1) (hb : dist o b = 1)
    (hza : dist z a ^ 2 ≤ dist z o ^ 2 + 1)
    (hzb : dist z b ^ 2 ≤ dist z o ^ 2 + 1)
    {s : ℝ} (hs : s ∈ Set.Icc (-1 : ℝ) 1) :
    dist z (axisSegment h a b s) ^ 2 = dist z o ^ 2 + s ^ 2 := by
  have upper (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
      dist z (axisSegment h a b t) ^ 2 ≤ dist z o ^ 2 + t ^ 2 := by
    let u := (t + 1) / 2
    have hu : u ∈ Set.Icc (0 : ℝ) 1 := axis_parameter ht
    have hc := CATZero.segment_cn h a b z hu
    change dist z (axisSegment h a b t) ^ 2 ≤ _ at hc
    rw [hab] at hc
    have hl := mul_le_mul_of_nonneg_left hza (sub_nonneg.mpr hu.2)
    have hr := mul_le_mul_of_nonneg_left hzb hu.1
    dsimp only [u] at *
    linarith
  have hneg : -s ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have hzero : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by norm_num
  have hsep : dist (axisSegment h a b s) (axisSegment h a b (-s)) = 2 * |s| := by
    rw [dist_axisSegment h hab hs hneg, show s - -s = 2 * s by ring, abs_mul]
    norm_num
  have hmid : o = CATZero.mid h (axisSegment h a b s) (axisSegment h a b (-s)) := by
    apply CATZero.eq_segment_of_dist h (t := 1/2) (by norm_num)
    · rw [← axisSegment_zero h hab ha hb, dist_axisSegment h hab hs hzero, hsep, sub_zero]
      ring
    · rw [← axisSegment_zero h hab ha hb, dist_axisSegment h hab hzero hneg, hsep, zero_sub,
        neg_neg]
      ring
  have hc := CATZero.mid_cn h (axisSegment h a b s) (axisSegment h a b (-s)) z
  rw [← hmid, hsep, mul_pow, sq_abs] at hc
  exact le_antisymm (upper s hs) (by linarith [upper (-s) hneg])

/-- The Euclidean cross-distance formula for all pairs of points on
distinct marked diameters, up to and including the endpoints. -/
theorem axis_cross_distance (h : CATZero X) (o : X) (x : Fin D → Bool → X)
    (hr : ∀ i b, dist o (x i b) ≤ 1)
    (hsum : ∑ i, dist (x i false) (x i true) = 2 * D)
    (hcross : ∀ i j, i ≠ j → ∀ a b, dist (x i a) (x j b) ≤ Real.sqrt 2)
    {i j : Fin D} (hij : i ≠ j) {s t : ℝ}
    (hs : s ∈ Set.Icc (-1 : ℝ) 1) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    dist (axisSegment h (x i false) (x i true) s) (axisSegment h (x j false) (x j true) t) ^ 2 =
      s ^ 2 + t ^ 2 := by
  obtain ⟨hd, hu⟩ := axis_diameters_and_radii o x hr hsum
  let p := axisSegment h (x i false) (x i true) s
  have hpo : dist p o = |s| := by
    rw [← axisSegment_zero h (hd i) (hu i false) (hu i true)]
    exact (dist_axisSegment h (hd i) hs (show (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 by norm_num)).trans
      (by rw [sub_zero])
  have hendpoint (b : Bool) : dist p (x j b) ^ 2 = 1 + s ^ 2 := by
    have hup (a : Bool) : dist (x j b) (x i a) ^ 2 ≤ dist (x j b) o ^ 2 + 1 := by
      have hsqrt := sq_le_sq₀ (dist_nonneg (x := x j b) (y := x i a)) (Real.sqrt_nonneg 2)
      have hsquare := hsqrt.mpr (hcross j i hij.symm b a)
      rw [Real.sq_sqrt (by norm_num)] at hsquare
      rw [dist_comm (x j b) o, hu]
      linarith
    rw [dist_comm]
    have he := axis_perpendicular_distance h (x j b) (hd i) (hu i false) (hu i true)
      (hup false) (hup true) hs
    simpa [p, dist_comm (x j b) o, hu] using he
  have hup (b : Bool) : dist p (x j b) ^ 2 ≤ dist p o ^ 2 + 1 := by
    rw [hendpoint, hpo, sq_abs]
    linarith
  have he := axis_perpendicular_distance h p (hd j) (hu j false) (hu j true)
    (hup false) (hup true) ht
  rwa [hpo, sq_abs] at he

end SpectralBooks
end LinearAlgebra
end OAI

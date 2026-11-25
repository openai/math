import OAI.Geometry.HyperbolicGroups.TangentRay

namespace OAI
/-! # Radial clipping in the port graph estimate -/

namespace ThreeFlat

open HyperbolicObstruction

/-- Clip each radius to `R` along the CAT(0) segment from the center. The
distance removed is the excess radius, and the map is 2-Lipschitz. -/
theorem exists_port_clip {X : Type*} [MetricSpace X] (hX : CATZero X)
    (o : X) {R : ℝ} (hR : 0 ≤ R) :
    ∃ p : X → X, (∀ x, dist (p x) o ≤ R) ∧
      (∀ x, dist x (p x) = max (dist x o - R) 0) ∧
      (∀ x y, dist (p x) (p y) ≤ 2 * dist x y) := by
  let t (x : X) : ℝ := if dist o x ≤ R then 1 else R / dist o x
  have ht (x : X) : t x ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [t]
    split_ifs with hx
    · exact ⟨zero_le_one, le_rfl⟩
    · have hp := hR.trans_lt (lt_of_not_ge hx)
      exact ⟨div_nonneg hR hp.le, (div_le_one hp).mpr (lt_of_not_ge hx).le⟩
  have htDist (x : X) : t x * dist o x = min (dist o x) R := by
    dsimp [t]
    split_ifs with hx
    · simp [min_eq_left hx]
    · have hp := hR.trans_lt (lt_of_not_ge hx)
      rw [min_eq_right (lt_of_not_ge hx).le, div_mul_cancel₀ _ hp.ne']
  let p (x : X) := CATZero.segment hX o x (t x)
  refine ⟨p, ?_, ?_, ?_⟩
  · intro x
    rw [dist_comm]
    exact (CATZero.segment_left hX o x (ht x)).trans_le
      ((htDist x).trans_le (min_le_right _ _))
  · intro x
    rw [dist_comm x (p x), dist_comm x o, CATZero.segment_right hX o x (ht x),
      sub_mul, one_mul, htDist]
    by_cases hx : dist o x ≤ R
    · rw [min_eq_left hx, sub_self, max_eq_right (sub_nonpos.mpr hx)]
    · rw [min_eq_right (lt_of_not_ge hx).le, max_eq_left (sub_nonneg.mpr (lt_of_not_ge hx).le)]
  · have ordered (x y : X) (hxy : dist o x ≤ dist o y) :
        dist (p x) (p y) ≤ 2 * dist x y := by
      have hfirst : t y * dist o x ≤ min (dist o x) R := by
        apply le_min
        · exact mul_le_of_le_one_left dist_nonneg (ht y).2
        · calc
            _ ≤ t y * dist o y := mul_le_mul_of_nonneg_left hxy (ht y).1
            _ = _ := htDist y
            _ ≤ _ := min_le_right _ _
      have hdiff : |t x - t y| * dist o x ≤ dist o y - dist o x := by
        calc
          _ = |(t x - t y) * dist o x| := by rw [abs_mul, abs_of_nonneg dist_nonneg]
          _ = min (dist o x) R - t y * dist o x := by
            rw [sub_mul, htDist, abs_of_nonneg (sub_nonneg.mpr hfirst)]
          _ ≤ min (dist o y) R - t y * dist o x :=
            sub_le_sub_right (min_le_min_right R hxy) _
          _ = t y * (dist o y - dist o x) := by rw [← htDist y, mul_sub]
          _ ≤ _ := mul_le_of_le_one_left (sub_nonneg.mpr hxy) (ht y).2
      calc
        dist (p x) (p y) ≤ dist (p x) (CATZero.segment hX o x (t y)) +
            dist (CATZero.segment hX o x (t y)) (p y) := dist_triangle ..
        _ ≤ (dist o y - dist o x) + t y * dist x y := by
          apply add_le_add
          · simpa only [p, CATZero.segment_dist hX o x (ht x) (ht y)] using hdiff
          · exact CATZero.radial_contraction hX o x y (ht y)
        _ ≤ _ := by
          have := mul_le_of_le_one_left (dist_nonneg : 0 ≤ dist x y) (ht y).2
          linarith [dist_triangle o x y]
    intro x y
    rcases le_total (dist o x) (dist o y) with h | h
    · exact ordered x y h
    · simpa only [dist_comm (p y) (p x), dist_comm y x] using ordered y x h

end ThreeFlat

end OAI

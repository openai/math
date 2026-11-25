import OAI.Geometry.HyperbolicGroups.TangentRay

namespace OAI
/-! # Contracting two segments by the same arclength

In a CAT(0) space, advancing two points toward a common endpoint by the
same distance contracts their separation. The two fractional segment
parameters may differ.
-/

namespace ThreeFlat

open HyperbolicObstruction

/-- Moving each point distance `t` toward `e` contracts the distance between
the points as long as neither has reached the common endpoint. -/
theorem dist_radial_step_le {X : Type*} [MetricSpace X] (h : CATZero X)
    (e x y : X) {t : ℝ} (ht : 0 ≤ t) (hx : t < dist e x) (hy : t < dist e y) :
    dist (CATZero.segment h e x (1 - t / dist e x))
      (CATZero.segment h e y (1 - t / dist e y)) ≤ dist x y := by
  let a := dist e x
  let b := dist e y
  have ha : 0 < a := ht.trans_lt hx
  have hb : 0 < b := ht.trans_lt hy
  have hs : 1 - t / a ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨sub_nonneg.mpr ((div_le_one ha).mpr hx.le), sub_le_self _ (div_nonneg ht ha.le)⟩
  have hu : 1 - t / b ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨sub_nonneg.mpr ((div_le_one hb).mpr hy.le), sub_le_self _ (div_nonneg ht hb.le)⟩
  have hsub : |(1 - t / a) - (1 - t / b)| * b = t / a * |a - b| := by
    calc
      _ = |((1 - t / a) - (1 - t / b)) * b| := by rw [abs_mul, abs_of_pos hb]
      _ = |t / a * (a - b)| := by
        congr 1
        field_simp [ha.ne', hb.ne']; ring
      _ = _ := by rw [abs_mul, abs_of_nonneg (div_nonneg ht ha.le)]
  have hab : |a - b| ≤ dist x y := by
    simpa only [a, b, dist_comm x e, dist_comm y e] using abs_dist_sub_le x y e
  calc
    _ ≤ dist (CATZero.segment h e x (1 - t / a)) (CATZero.segment h e y (1 - t / a))
          + dist (CATZero.segment h e y (1 - t / a)) (CATZero.segment h e y (1 - t / b)) :=
      dist_triangle _ _ _
    _ ≤ (1 - t / a) * dist x y + |(1 - t / a) - (1 - t / b)| * b :=
      add_le_add (CATZero.radial_contraction h e x y hs) (CATZero.segment_dist h e y hs hu).le
    _ ≤ (1 - t / a) * dist x y + t / a * dist x y := by
      rw [hsub]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hab (div_nonneg ht ha.le))
    _ = dist x y := by ring

end ThreeFlat

end OAI

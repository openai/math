import OAI.Geometry.HyperbolicGroups.MetricProduct
import OAI.ThreeFlat.RadialContraction

namespace OAI
/-! # Geodesic rays to a common escaping endpoint

The endpoint may escape every pointed ball, while each point at fixed
arclength along a segment to it has a bounded representative. Two such rays
stay within the distance between their origins at every common time.
-/

noncomputable section

namespace ThreeFlat

open Filter Topology HyperbolicObstruction MetricLimit

variable {X : ℕ → Type*} [∀ n, MetricSpace (X n)] {o : ∀ n, X n} {U : Ultrafilter ℕ}
variable (hX : ∀ n, CATZero (X n)) (E : ∀ n, X n)

private theorem stepParameter_mem {t d : ℝ} (ht : 0 ≤ t) (hd : t < d) :
    1 - t / d ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨sub_nonneg.mpr ((div_le_one (ht.trans_lt hd)).mpr hd.le),
   sub_le_self _ (div_nonneg ht (ht.trans hd.le))⟩

/-- Move from the representative a distance `t` towards the endpoint.
When the segment is too short, use the original representative. -/
def rayRep (x : Bounded U X o) (t : ℝ) : Bounded U X o where
  val n := if 0 ≤ t ∧ t < dist (E n) (x.val n) then
    CATZero.segment (hX n) (E n) (x.val n) (1 - t / dist (E n) (x.val n))
    else x.val n
  bound := by
    obtain ⟨R, hR⟩ := x.bound
    refine ⟨R + |t|, fun n ↦ ?_⟩
    split_ifs with h
    · apply (dist_triangle _ (x.val n) _).trans
      apply add_le_add (hR n)
      rw [dist_comm, CATZero.segment_right (hX n) _ _ (stepParameter_mem h.1 h.2),
        sub_sub_cancel, div_mul_cancel₀ _ (h.1.trans_lt h.2).ne', abs_of_nonneg h.1]
    · linarith [hR n, abs_nonneg t]

/-- The corresponding point of the separated ultralimit. -/
def rayPoint (x : Bounded U X o) (t : ℝ) : Space (U := U) (X := X) (o := o) :=
  point (rayRep hX E x t)

@[simp] theorem rayPoint_zero (x : Bounded U X o) : rayPoint hX E x 0 = point x := by
  apply congrArg point
  ext n
  change (if 0 ≤ (0 : ℝ) ∧ 0 < dist (E n) (x.val n) then _ else _) = _
  split_ifs
  · simpa using (CATZero.segment_spec (hX n) (E n) (x.val n)).2.1
  · rfl

omit hX in
private theorem eventually_lt_endpoint_dist (x : Bounded U X o)
    (hE : Tendsto (fun n ↦ dist (o n) (E n)) (U : Filter ℕ) atTop) (t : ℝ) :
    ∀ᶠ n in (U : Filter ℕ), t < dist (E n) (x.val n) := by
  obtain ⟨R, hR⟩ := x.bound
  filter_upwards [hE.eventually_gt_atTop (t + R)] with n hn
  have h := dist_triangle (o n) (x.val n) (E n)
  rw [dist_comm (x.val n)] at h
  linarith [hR n]

/-- Along an escaping endpoint, the distance remaining on the finite
segment decreases by exactly the chosen arclength on an ultrafilter-large set. -/
theorem rayRep_eventually_dist_endpoint (x : Bounded U X o)
    (hE : Tendsto (fun n ↦ dist (o n) (E n)) (U : Filter ℕ) atTop) {t : ℝ} (ht : 0 ≤ t) :
    ∀ᶠ n in (U : Filter ℕ), dist (E n) ((rayRep hX E x t).val n) = dist (E n) (x.val n) - t := by
  filter_upwards [eventually_lt_endpoint_dist E x hE t] with n hn
  simp only [rayRep, ite_eq_left (And.intro ht hn)]
  rw [CATZero.segment_left (hX n) _ _ (stepParameter_mem ht hn), sub_mul, one_mul,
    div_mul_cancel₀ _ (ht.trans_lt hn).ne']

/-- The ultralimit ray preserves arclength. -/
theorem rayPoint_dist (x : Bounded U X o)
    (hE : Tendsto (fun n ↦ dist (o n) (E n)) (U : Filter ℕ) atTop)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    dist (rayPoint hX E x s) (rayPoint hX E x t) = |s - t| := by
  apply tendsto_nhds_unique (tendsto_point_dist _ _)
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_lt_endpoint_dist E x hE s, eventually_lt_endpoint_dist E x hE t]
    with n hns hnt
  symm
  simp only [rayRep, ite_eq_left (And.intro hs hns), ite_eq_left (And.intro ht hnt)]
  rw [CATZero.segment_dist (hX n) _ _ (stepParameter_mem hs hns) (stepParameter_mem ht hnt),
    show (1 - s / dist (E n) (x.val n)) - (1 - t / dist (E n) (x.val n)) =
      -((s - t) / dist (E n) (x.val n)) by ring, abs_neg, abs_div,
    abs_of_nonneg dist_nonneg, div_mul_cancel₀ _ (hs.trans_lt hns).ne']

/-- Rays toward the same endpoint remain at bounded distance uniformly for all time. -/
theorem rayPoint_dist_le (x y : Bounded U X o)
    (hE : Tendsto (fun n ↦ dist (o n) (E n)) (U : Filter ℕ) atTop) {t : ℝ} (ht : 0 ≤ t) :
    dist (rayPoint hX E x t) (rayPoint hX E y t) ≤ dist (point x) (point y) := by
  apply le_of_tendsto_of_tendsto (tendsto_point_dist _ _) (tendsto_point_dist x y)
  filter_upwards [eventually_lt_endpoint_dist E x hE t, eventually_lt_endpoint_dist E y hE t]
    with n hx hy
  simpa only [rayRep, ite_eq_left (And.intro ht hx), ite_eq_left (And.intro ht hy)] using
    dist_radial_step_le (hX n) (E n) (x.val n) (y.val n) ht hx hy

end ThreeFlat

end
end OAI

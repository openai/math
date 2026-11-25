import OAI.Geometry.HyperbolicGroups.MetricProduct

namespace OAI
/-! # Normalized distances to endpoints in a pointed ultralimit

Subtracting the distance from the base point gives a bounded value on every
bounded section, even for endpoints that escape to infinity.
-/

noncomputable section

namespace ThreeFlat

open Filter Topology HyperbolicObstruction.MetricLimit

variable (U : Ultrafilter ℕ) {X : ℕ → Type*} [∀ n, MetricSpace (X n)]
  {o : ∀ n, X n} (E : ∀ n, X n)

private def sectionPotential (x : Bounded U X o) : ℝ :=
  limUnder (U : Filter ℕ) (fun n ↦ dist (E n) (x.val n) - dist (E n) (o n))

private theorem tendsto_sectionPotential (x : Bounded U X o) :
    Tendsto (fun n ↦ dist (E n) (x.val n) - dist (E n) (o n)) U
      (𝓝 (sectionPotential U E x)) := by
  obtain ⟨R, hR⟩ := x.bound
  let f := fun n ↦ dist (E n) (x.val n) - dist (E n) (o n)
  have hb : Metric.closedBall (0 : ℝ) R ∈ U.map f := by
    change ∀ᶠ n in (U : Filter ℕ), dist (f n) 0 ≤ R
    apply Eventually.of_forall
    intro n
    rw [Real.dist_eq, sub_zero]
    have h := abs_dist_sub_le (x.val n) (o n) (E n)
    rw [dist_comm (x.val n) (E n), dist_comm (o n) (E n), dist_comm (x.val n) (o n)] at h
    exact h.trans (hR n)
  obtain ⟨a, _, ha⟩ := (isCompact_closedBall (0 : ℝ) R).ultrafilter_le_nhds' (U.map f) hb
  exact tendsto_nhds_limUnder ⟨a, ha⟩

private theorem dist_sectionPotential_le (x y : Bounded U X o) :
    dist (sectionPotential U E x) (sectionPotential U E y) ≤ dist (point x) (point y) := by
  apply le_of_tendsto_of_tendsto' ((tendsto_sectionPotential U E x).dist
    (tendsto_sectionPotential U E y)) (tendsto_point_dist x y)
  intro n
  rw [Real.dist_eq, sub_sub_sub_cancel_right, dist_comm (E n) (x.val n),
    dist_comm (E n) (y.val n)]
  exact abs_dist_sub_le _ _ _

/-- The limiting distance to the endpoints, normalized to zero at the base point. -/
def endpointPotential : Space (U := U) (X := X) (o := o) → ℝ :=
  SeparationQuotient.lift (sectionPotential U E) fun x y h ↦ by
    have he : point x = point y := SeparationQuotient.mk_eq_mk.mpr h
    have hd := dist_sectionPotential_le U E x y
    rw [he, dist_self] at hd
    exact dist_le_zero.mp hd

/-- Every bounded sequence of points computes the potential of its ultralimit. -/
theorem tendsto_endpointPotential (x : Bounded U X o) :
    Tendsto (fun n ↦ dist (E n) (x.val n) - dist (E n) (o n)) U
      (𝓝 (endpointPotential U E (point x))) :=
  tendsto_sectionPotential U E x

/-- The limiting potential is 1-Lipschitz. -/
theorem abs_endpointPotential_sub_le (x y : Space (U := U) (X := X) (o := o)) :
    |endpointPotential U E x - endpointPotential U E y| ≤ dist x y := by
  obtain ⟨p, rfl⟩ := SeparationQuotient.surjective_mk x
  obtain ⟨q, rfl⟩ := SeparationQuotient.surjective_mk y
  exact (Real.dist_eq (sectionPotential U E p) (sectionPotential U E q) ▸
    dist_sectionPotential_le U E p q)

theorem lipschitzWith_endpointPotential :
    LipschitzWith 1 (endpointPotential U (o := o) E) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using
    abs_endpointPotential_sub_le U E x y

/-- Differences of endpoint distances converge without choosing a common normalization. -/
theorem tendsto_endpointPotential_sub (x y : Bounded U X o) :
    Tendsto (fun n ↦ dist (E n) (x.val n) - dist (E n) (y.val n)) U
      (𝓝 (endpointPotential U E (point x) - endpointPotential U E (point y))) := by
  simpa only [sub_sub_sub_cancel_right] using
    (tendsto_endpointPotential U E x).sub (tendsto_endpointPotential U E y)

/-- For sections with vanishing broken-path excess, the difference of the two
endpoint distances changes by twice the difference of the first potential. -/
theorem tendsto_endpoint_phase_difference (A B : ∀ n, X n) (x y : Bounded U X o)
    (hx : Tendsto (fun n ↦ dist (A n) (x.val n) + dist (B n) (x.val n) -
      dist (A n) (B n)) U (𝓝 0))
    (hy : Tendsto (fun n ↦ dist (A n) (y.val n) + dist (B n) (y.val n) -
      dist (A n) (B n)) U (𝓝 0)) :
    Tendsto (fun n ↦ (dist (A n) (x.val n) - dist (B n) (x.val n)) -
      (dist (A n) (y.val n) - dist (B n) (y.val n))) U
      (𝓝 (2 * (endpointPotential U A (point x) - endpointPotential U A (point y)))) := by
  have ht := ((tendsto_endpointPotential_sub U A x y).const_mul 2).sub (hx.sub hy)
  rw [sub_self, sub_zero] at ht
  exact ht.congr (fun n ↦ by ring)

end ThreeFlat

end
end OAI

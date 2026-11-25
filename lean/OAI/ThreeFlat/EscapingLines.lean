import OAI.ThreeFlat.Horofunction
import OAI.ThreeFlat.EscapingRay

namespace OAI
/-! # Lines from two escaping endpoints

If the broken paths from `A` to `B` through a marked point have vanishing excess,
that point minimizes the sum of the two endpoint potentials in the ultralimit.
The two rays through it join to form a line on which the two potentials have
opposite unit slopes. Lines constructed from the same pair of endpoint sequences
remain at bounded synchronous distance.
-/

noncomputable section
namespace ThreeFlat

open Filter Topology HyperbolicObstruction MetricLimit

variable {X : ℕ → Type*} [∀ n, MetricSpace (X n)] {o : ∀ n, X n} {U : Ultrafilter ℕ}

/-- A marked point whose broken-path excess vanishes minimizes the sum of the
normalized distance functions on the whole limiting space. -/
theorem endpointPotential_sum_min (A B : ∀ n, X n) (x : Bounded U X o)
    (he : Tendsto (fun n ↦ dist (A n) (x.val n) + dist (B n) (x.val n) - dist (A n) (B n))
      (U : Filter ℕ) (𝓝 0)) (z : Space (U := U) (X := X) (o := o)) :
    endpointPotential U A (point x) + endpointPotential U B (point x) ≤
      endpointPotential U A z + endpointPotential U B z := by
  obtain ⟨y, rfl⟩ := SeparationQuotient.surjective_mk z
  have h := ((tendsto_endpointPotential U A x).add (tendsto_endpointPotential U B x)).sub he
  rw [sub_zero] at h
  apply le_of_tendsto_of_tendsto' h ((tendsto_endpointPotential U A y).add
    (tendsto_endpointPotential U B y))
  intro n
  have ht := dist_triangle_right (A n) (B n) (y.val n)
  linarith

variable (hX : ∀ n, CATZero (X n))

/-- The endpoint potential aimed at by a ray decreases by its arclength. -/
theorem endpointPotential_rayPoint (E : ∀ n, X n) (x : Bounded U X o)
    (hE : Tendsto (fun n ↦ dist (o n) (E n)) (U : Filter ℕ) atTop) {t : ℝ} (ht : 0 ≤ t) :
    endpointPotential U E (rayPoint hX E x t) = endpointPotential U E (point x) - t := by
  apply tendsto_nhds_unique (tendsto_endpointPotential U E (rayRep hX E x t))
  apply ((tendsto_endpointPotential U E x).sub_const t).congr'
  filter_upwards [rayRep_eventually_dist_endpoint hX E x hE ht] with n hn
  linarith

private theorem endpointPotential_opposite_ray (A B : ∀ n, X n) (x : Bounded U X o)
    (hB : Tendsto (fun n ↦ dist (o n) (B n)) (U : Filter ℕ) atTop)
    (he : Tendsto (fun n ↦ dist (A n) (x.val n) + dist (B n) (x.val n) - dist (A n) (B n))
      (U : Filter ℕ) (𝓝 0)) {t : ℝ} (ht : 0 ≤ t) :
    endpointPotential U A (rayPoint hX B x t) = endpointPotential U A (point x) + t := by
  have hm := endpointPotential_sum_min A B x he (rayPoint hX B x t)
  rw [endpointPotential_rayPoint hX B x hB ht] at hm
  have hl := abs_endpointPotential_sub_le U A (rayPoint hX B x t) (point x)
  have hd := rayPoint_dist hX B x hB ht (show (0 : ℝ) ≤ 0 from le_rfl)
  rw [rayPoint_zero, sub_zero, abs_of_nonneg ht] at hd
  linarith [(abs_le.mp (hl.trans hd.le)).2]

/-- The two limiting rays, joined at the mark and oriented toward `B`. -/
def escapingLine (A B : ∀ n, X n) (x : Bounded U X o) (t : ℝ) :
    Space (U := U) (X := X) (o := o) :=
  if 0 ≤ t then rayPoint hX B x t else rayPoint hX A x (-t)

@[simp] theorem escapingLine_zero (A B : ∀ n, X n) (x : Bounded U X o) :
    escapingLine hX A B x 0 = point x := by simp [escapingLine, rayPoint_zero]

/-- Both normalized endpoint distances vary affinely along the limiting line. -/
theorem endpointPotential_escapingLine (A B : ∀ n, X n) (x : Bounded U X o)
    (hA : Tendsto (fun n ↦ dist (o n) (A n)) (U : Filter ℕ) atTop)
    (hB : Tendsto (fun n ↦ dist (o n) (B n)) (U : Filter ℕ) atTop)
    (he : Tendsto (fun n ↦ dist (A n) (x.val n) + dist (B n) (x.val n) - dist (A n) (B n))
      (U : Filter ℕ) (𝓝 0)) (t : ℝ) :
    endpointPotential U A (escapingLine hX A B x t) = endpointPotential U A (point x) + t ∧
    endpointPotential U B (escapingLine hX A B x t) = endpointPotential U B (point x) - t := by
  by_cases ht : 0 ≤ t
  · simp only [escapingLine, ite_eq_left ht]
    exact ⟨endpointPotential_opposite_ray hX A B x hB he ht, endpointPotential_rayPoint hX B x hB ht⟩
  · simp only [escapingLine, ite_eq_right ht]
    have he' : Tendsto (fun n ↦ dist (B n) (x.val n) + dist (A n) (x.val n) - dist (B n) (A n))
        (U : Filter ℕ) (𝓝 0) := by simpa only [add_comm, dist_comm (B _) (A _)] using he
    have hn : 0 ≤ -t := neg_nonneg.mpr (le_of_not_ge ht)
    constructor
    · simpa only [sub_neg_eq_add] using endpointPotential_rayPoint hX A x hA hn
    · simpa only [sub_eq_add_neg] using endpointPotential_opposite_ray hX B A x hA he' hn

/-- Vanishing excess prevents a corner where the rays through the marked point meet. -/
theorem escapingLine_isometry (A B : ∀ n, X n) (x : Bounded U X o)
    (hA : Tendsto (fun n ↦ dist (o n) (A n)) (U : Filter ℕ) atTop)
    (hB : Tendsto (fun n ↦ dist (o n) (B n)) (U : Filter ℕ) atTop)
    (he : Tendsto (fun n ↦ dist (A n) (x.val n) + dist (B n) (x.val n) - dist (A n) (B n))
      (U : Filter ℕ) (𝓝 0)) : Isometry (escapingLine hX A B x) := by
  let l := escapingLine hX A B x
  have mixed {s t : ℝ} (hs : 0 ≤ s) (ht : t < 0) : dist (l s) (l t) = |s-t| := by
    have hn : 0 ≤ -t := neg_nonneg.mpr ht.le
    have ds := rayPoint_dist hX B x hB hs (t := 0) le_rfl
    have dt := rayPoint_dist hX A x hA (s := 0) le_rfl hn
    rw [rayPoint_zero, sub_zero, abs_of_nonneg hs] at ds
    rw [rayPoint_zero, zero_sub, neg_neg, abs_of_neg ht] at dt
    have upper : dist (l s) (l t) ≤ s + -t := calc
      _ ≤ dist (l s) (point x) + dist (point x) (l t) := dist_triangle _ _ _
      _ = _ := by simp only [l, escapingLine, ite_eq_left hs, ite_eq_right (not_le.mpr ht), ds, dt]
    have lower := abs_endpointPotential_sub_le U A (l s) (l t)
    rw [(endpointPotential_escapingLine hX A B x hA hB he s).1,
      (endpointPotential_escapingLine hX A B x hA hB he t).1, add_sub_add_left_eq_sub] at lower
    exact le_antisymm (by rw [abs_of_nonneg (by linarith : 0 ≤ s-t)]; linarith) lower
  apply Isometry.of_dist_eq
  intro s t
  rw [Real.dist_eq]
  by_cases hs : 0 ≤ s <;> by_cases ht : 0 ≤ t
  · simpa only [escapingLine, ite_eq_left hs, ite_eq_left ht] using rayPoint_dist hX B x hB hs ht
  · exact mixed hs (lt_of_not_ge ht)
  · rw [dist_comm, abs_sub_comm]
    exact mixed ht (lt_of_not_ge hs)
  · simp only [escapingLine, ite_eq_right hs, ite_eq_right ht]
    rw [rayPoint_dist hX A x hA (neg_nonneg.mpr (le_of_not_ge hs))
      (neg_nonneg.mpr (le_of_not_ge ht)), neg_sub_neg, abs_sub_comm]

/-- Lines arising from a common pair of escaping endpoint sequences are parallel. -/
theorem escapingLine_dist_le (A B : ∀ n, X n) (x y : Bounded U X o)
    (hA : Tendsto (fun n ↦ dist (o n) (A n)) (U : Filter ℕ) atTop)
    (hB : Tendsto (fun n ↦ dist (o n) (B n)) (U : Filter ℕ) atTop) (t : ℝ) :
    dist (escapingLine hX A B x t) (escapingLine hX A B y t) ≤ dist (point x) (point y) := by
  by_cases ht : 0 ≤ t
  · simpa only [escapingLine, ite_eq_left ht] using rayPoint_dist_le hX B x y hB ht
  · simpa only [escapingLine, ite_eq_right ht] using rayPoint_dist_le hX A x y hA (neg_nonneg.mpr (le_of_not_ge ht))

end ThreeFlat

end
end OAI

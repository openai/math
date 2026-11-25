import OAI.HyperbolicObstruction.ParallelShift

namespace OAI
/-! # A single signed coordinate shared by parallel oriented axes -/

namespace Hierarchy.AdaptiveProbe
open HyperbolicObstruction
noncomputable section

variable {X : Type*} [MetricSpace X]

def calibration (r : ℝ → X) (x : X) := ⨆ t : ℝ, t-dist x (r t)

private theorem reading_bdd (r : ℝ → X) (hr : Isometry r) (x : X) :
    BddAbove (Set.range fun t : ℝ => t-dist x (r t)) := by
  refine ⟨dist (r 0) x, ?_⟩
  rintro _ ⟨t,rfl⟩
  have tri := dist_triangle (r 0) x (r t)
  rw [hr.dist_eq, Real.dist_eq, zero_sub,abs_neg] at tri
  linarith [le_abs_self t]

theorem calibration_lipschitz (r : ℝ → X) (hr : Isometry r) : LipschitzWith 1 (calibration r) := by
  have side (x y : X) : calibration r x ≤ calibration r y+dist x y := by
    apply ciSup_le
    intro t
    have lower := le_ciSup (reading_bdd r hr y) t
    change t-dist y (r t) ≤ calibration r y at lower
    have tri := dist_triangle y x (r t)
    rw [dist_comm y x] at tri
    linarith
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq,NNReal.coe_one,one_mul,abs_le]
  constructor
  · have h := side y x
    rw [dist_comm y x] at h
    linarith
  · linarith [side x y]

/-- Translating both parameters leaves the distance of the parallel lines
unchanged. Consequently transfer of the common coordinate is exact even
when the lines' marked origins have different phases. -/
theorem calibration_parallel (C : CATZero X) (r l : ℝ → X) (hr : Isometry r)
    (hl : Isometry l) (parallel : ∃ K : ℝ, ∀ t, dist (l t) (r t) ≤ K) (s : ℝ) :
    calibration r (l s) = calibration r (l 0) + s := by
  have shift (t : ℝ) : dist (l s) (r (t+s)) = dist (l 0) (r t) := by
    simpa only [zero_add] using CATZero.dist_parallel_shift C hl hr parallel 0 t s
  apply le_antisymm
  · apply ciSup_le
    intro t
    have eq := shift (t-s)
    rw [sub_add_cancel] at eq
    rw [eq]
    have lower := le_ciSup (reading_bdd r hr (l 0)) (t-s)
    change t-s-dist (l 0) (r (t-s)) ≤ calibration r (l 0) at lower
    linarith
  · have bound : calibration r (l 0) ≤ calibration r (l s) - s := by
      apply ciSup_le
      intro t
      have lower := le_ciSup (reading_bdd r hr (l s)) (t+s)
      change t+s-dist (l s) (r (t+s)) ≤ calibration r (l s) at lower
      rw [shift] at lower
      linarith
    linarith

end
end Hierarchy.AdaptiveProbe

end OAI

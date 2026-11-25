import OAI.ThreeFlat.ExpanderCloudEnergy

namespace OAI
/-! # Comparison with the energy of a lazy barycentric step -/

namespace ThreeFlat.Expander

open Finset

variable {V X : Type*} [Fintype V] [DecidableEq V] [PseudoMetricSpace X]

/-- Comparing both ends of each edge through a single intermediate point at
its starting vertex bounds the original energy by the lazy step energy. -/
theorem energy_le_lazy_crossEnergy (G : Matrix V V ℝ) (hG : G ∈ Matrix.rowStochastic ℝ V)
    (y z : V → X) :
    energy G y ≤ 4 * avg (fun i => ∑ j, ((1/2 : ℝ) • (1+G)) i j * dist (z i) (y j)^2) := by
  rw [← avg_mul]
  apply avg_le
  intro i
  let d (j : V) := dist (z i) (y j)^2
  have bound (j : V) : dist (y i) (y j)^2 ≤ 2 * (d i + d j) := by
    have h := dist_triangle (y i) (z i) (y j)
    rw [dist_comm (y i) (z i)] at h
    have hs := pow_le_pow_left₀ dist_nonneg h 2
    dsimp only [d]
    nlinarith only [hs, sq_nonneg (dist (z i) (y i) - dist (z i) (y j))]
  have hI : ∑ j, (1 : Matrix V V ℝ) i j * d j = d i := by
    simp [Matrix.one_apply, ite_mul]
  calc
    _ ≤ ∑ j, G i j * (2 * (d i + d j)) :=
      sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (bound j)
        (Matrix.nonneg_of_mem_rowStochastic hG)
    _ = 2 * (d i + ∑ j, G i j * d j) := by
      simp_rw [mul_left_comm (G i _) 2, mul_add]
      rw [sum_add_distrib, ← mul_sum, ← mul_sum, ← sum_mul,
        Matrix.sum_row_of_mem_rowStochastic hG, one_mul]
    _ = 4 * ∑ j, ((1/2 : ℝ) • (1+G)) i j * d j := by
      simp_rw [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, mul_assoc, add_mul]
      rw [← mul_sum, sum_add_distrib, hI]
      ring

end ThreeFlat.Expander

end OAI

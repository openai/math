import OAI.ThreeFlat.ExpanderBasic

namespace OAI
/-! # Lazy transition matrices and their Cesàro averages -/

noncomputable section
namespace ThreeFlat.Expander

open Finset Matrix

variable {V X : Type*} [Fintype V] [DecidableEq V] [PseudoMetricSpace X]

/-- Holding with probability one half makes the barycentric update control the
displacement from the previous placement at the same vertex. -/
def lazyStep (G : Matrix V V ℝ) : Matrix V V ℝ := (1/2 : ℝ) • (1 + G)

/-- Average transition matrix at times one through `t`. -/
def cesaro (A : Matrix V V ℝ) (t : ℕ) : Matrix V V ℝ :=
  (1/(t : ℝ)) • ∑ h ∈ range t, A ^ (h+1)

theorem lazyStep_row {G : Matrix V V ℝ} (hG : G ∈ rowStochastic ℝ V) :
    lazyStep G ∈ rowStochastic ℝ V := by
  unfold lazyStep
  rw [smul_add]
  apply Matrix.convex_rowStochastic (one_mem _) hG <;> norm_num

theorem lazyStep_col {G : Matrix V V ℝ} (hG : G ∈ colStochastic ℝ V) :
    lazyStep G ∈ colStochastic ℝ V := by
  unfold lazyStep
  rw [smul_add]
  apply Matrix.convex_colStochastic (one_mem _) hG <;> norm_num

theorem energy_cesaro (A : Matrix V V ℝ) (t : ℕ) (x : V → X) :
    energy (cesaro A t) x = (∑ h ∈ range t, energy (A^(h+1)) x) / t := by
  have smulEnergy (c : ℝ) (M : Matrix V V ℝ) : energy (c • M) x = c * energy M x := by
    simp only [energy, Matrix.smul_apply, smul_eq_mul, mul_assoc, ← mul_sum, avg_mul]
  have addEnergy (M N : Matrix V V ℝ) : energy (M+N) x = energy M x + energy N x := by
    simp only [energy, Matrix.add_apply, add_mul, sum_add_distrib, avg_add]
  have sumEnergy (n : ℕ) :
      energy (∑ h ∈ range n, A^(h+1)) x = ∑ h ∈ range n, energy (A^(h+1)) x := by
    induction n with
    | zero => simp [energy, avg]
    | succ n ih => rw [sum_range_succ, sum_range_succ, addEnergy, ih]
  rw [cesaro, smulEnergy, sumEnergy]
  ring

end ThreeFlat.Expander

end
end OAI

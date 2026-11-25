import OAI.LinearAlgebra.FiniteFourier.GridInputs

/-! # The fixed-convolution circuit estimate used for grid factors -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open ExactFourier.CoefficientTime

/-- Integral gate budget corresponding to the real estimate. -/
noncomputable def convolutionBudget (β C : ℝ) (n : ℕ) : ℕ :=
  ⌊C * n * (1 + Real.logb 2 n) ^ β⌋₊

theorem convolutionBudget_le {β C : ℝ} (hC : 0 ≤ C) {n : ℕ} (hn : 0 < n) :
    (convolutionBudget β C n : ℝ) ≤ C * n * (1 + Real.logb 2 n) ^ β := by
  have hone : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog := Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) hone
  exact Nat.floor_le (mul_nonneg (mul_nonneg hC (Nat.cast_nonneg n))
    (Real.rpow_nonneg (by linarith) _))

theorem FixedConvolutionBound.realizable {K : Type*} [Field K] {β C : ℝ}
    (h : FixedConvolutionBound K β C) (n : ℕ) (f : PowerSeries K) :
    RealizableAtMost (truncMatrix n f) (convolutionBudget β C n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨0, Nat.zero_le _, ⟨.nil, fun _ ↦ .zero⟩, ?_⟩
    ext i
    exact i.elim0
  · exact (complexity_le_iff ..).mp (Nat.le_floor (h n hn f))

end FiniteFourier
end LinearAlgebra
end OAI

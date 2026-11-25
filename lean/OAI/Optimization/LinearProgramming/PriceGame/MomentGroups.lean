import OAI.Optimization.LinearProgramming.PriceGame.MomentLocal
import OAI.Optimization.LinearProgramming.PriceGame.MomentThreshold
import OAI.Optimization.LinearProgramming.PriceGame.MomentConstants

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Moment

open Finset

/-- The scores of the local experts after the probe half of one trial. -/
theorem local_rounded_moment {E : Type*} [Fintype E] (w : E → ℝ) (gain : ℕ → E → ℝ)
    (hw : ∀ e, 0 ≤ w e) (hg : ∀ t < probes, ∀ e, |gain t e| ≤ 1)
    (hbal : ∀ t < probes, ∑ e, localWeight eta w gain t e * gain t e = 0) :
    (∑ e, w e * (2 : ℝ) ^ roundedScore scale sigma ((∑ t ∈ range probes, gain t e) / probes)) ≤
      (2 : ℝ) ^ tau * ∑ e, w e := by
  apply roundedScore_moment _ _ hw scale_pos.le sigma_pos.le
    trialBranch_local.1 trialBranch_local.2
  have hbot : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hr : (probes : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr probes_pos.ne'
  have hmean (x : ℝ) :
      (2 : ℝ) ^ ((eta * probes / Real.log 2) * (x / probes)) = Real.exp (eta * x) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    congr 1
    field_simp [hbot, hr]
  have hscale :
      (2 : ℝ) ^ ((eta * probes / Real.log 2) * sigma / 8) = Real.exp (eta ^ 2 * probes) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    congr 1
    unfold eta
    field_simp [hbot]
  have hhalf : eta ≤ 1 / 2 := by
    have hpow : 1 ≤ (2 : ℝ) ^ 272 := one_le_pow₀ (by norm_num)
    have hsig : sigma ≤ 1 := by
      simpa [sigma] using (one_div_le_one_div_of_le zero_lt_one hpow)
    dsimp [eta]
    linarith
  simp only [hmean, hscale]
  exact local_exponential_estimate eta w gain probes hw eta_pos.le hhalf hg hbal

/-- Deeper experts accumulate child scores in both halves of the trial. -/
theorem deep_rounded_moment {E : Type*} [Fintype E] (w : E → ℝ) (s : ℕ → E → ℕ)
    (hw : ∀ e, 0 ≤ w e)
    (hstep : ∀ t < 2 * probes, (∑ e, deepWeight w s t e * 2 ^ s t e) ≤
      (2 : ℝ) ^ tau * ∑ e, deepWeight w s t e) :
    (∑ e, w e * (2 : ℝ) ^ roundedScore scale sigma
      ((∑ t ∈ range (2 * probes), (s t e : ℝ)) / (2 * (probes : ℝ)))) ≤
      (2 : ℝ) ^ tau * ∑ e, w e := by
  apply roundedScore_moment _ _ hw scale_pos.le sigma_pos.le
    trialBranch_deeper.1 trialBranch_deeper.2
  have hn : 2 * (probes : ℝ) ≠ 0 := mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr probes_pos.ne')
  have hterm (e : E) :
      (2 : ℝ) ^ ((2 * (probes : ℝ)) * ((∑ t ∈ range (2 * probes), (s t e : ℝ)) /
        (2 * (probes : ℝ)))) = (2 : ℝ) ^ ∑ t ∈ range (2 * probes), s t e := by
    rw [mul_comm (2 * (probes : ℝ)) _, div_mul_cancel₀ _ hn, ← Real.rpow_natCast]
    push_cast
    rfl
  have hrhs : (2 * (probes : ℝ)) * sigma / 8 = ((2 * probes : ℕ) : ℝ) * tau := by
    push_cast
    unfold tau
    ring
  simp only [hterm, hrhs]
  exact cumulative_deep_moment w s (2 * probes) tau hstep

end Moment
end PriceGame
end LinearProgramming
end Optimization
end OAI

import OAI.LinearAlgebra.FiniteFourier.BatchedRepetition

/-! # A single choice of delay length and error fractions for every batch size -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier
noncomputable section

def batchDelays (l : ℝ) := ⌊l / 64⌋₊

theorem batchDelays_bounds {l : ℝ} (hl : 1000 ≤ l) :
    l / 128 ≤ (batchDelays l : ℝ) ∧ (batchDelays l : ℝ) ≤ l / 64 := by
  unfold batchDelays
  exact ⟨by linarith [Nat.lt_floor_add_one (l/64)], Nat.floor_le (by linarith)⟩

theorem batchDelays_pos {l : ℝ} (hl : 1000 ≤ l) : 0 < batchDelays l := by
  have : 0 < (batchDelays l : ℝ) := by linarith [(batchDelays_bounds hl).1]
  exact_mod_cast this

theorem batch_delay_rank_budget {l h b : ℝ} (hl : 1000 ≤ l) (hh : 0 ≤ h) (hb : 0 ≤ b)
    {S : ℕ} (hs : (S:ℝ) < b/128 * h * l) :
    ((S + ⌊b*h⌋₊ * batchDelays l : ℕ) : ℝ) ≤ 2*b*(h * batchDelays l) := by
  have hf := Nat.floor_le (show 0 ≤ b*h by positivity)
  push_cast
  have h₁ := mul_le_mul_of_nonneg_left (batchDelays_bounds hl).1 (show 0 ≤ b*h by positivity)
  have h₂ := mul_le_mul_of_nonneg_right hf (Nat.cast_nonneg (α := ℝ) (batchDelays l))
  linarith

private theorem batch_short_support {l : ℝ} (hl : 1000 ≤ l) :
    let d := batchDelays l
    2 * (1 + (d:ℝ)*2^d*d) ≤ (2:ℝ)^(l/8) := by
  let d := batchDelays l
  have hd : (d:ℝ) ≤ (2:ℝ)^d := by exact_mod_cast d.lt_two_pow_self.le
  have h1 : (1:ℝ) ≤ (2:ℝ)^d := one_le_pow₀ (by norm_num)
  calc
    2 * (1 + (d:ℝ)*2^d*d) ≤ 2 * ((2:ℝ)^d*2^d*2^d + 2^d*2^d*2^d) := by
      have h3 : (1:ℝ) ≤ (2:ℝ)^d*2^d*2^d := one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le h1 h1) h1
      gcongr
    _ = (2:ℝ)^(3*d+2) := by rw [pow_add, pow_mul', pow_three]; ring
    _ ≤ (2:ℝ)^(l/8) := by
      rw [← Real.rpow_natCast]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith [(batchDelays_bounds hl).2]

theorem batch_delay_support_budget {l : ℝ} (hl : 1000 ≤ l) (h : ℕ) :
    let d := batchDelays l
    (h:ℝ)*d + repeatSupportBudget h d (1/4*h*(2:ℝ)^(l/8)) ≤
      ((h:ℝ)*d) * (2:ℝ)^(l/8) := by
  dsimp only [repeatSupportBudget]
  have hw := batch_short_support hl
  have hk := mul_le_mul_of_nonneg_left hw
    (show 0 ≤ (h:ℝ)*batchDelays l by positivity)
  have hp : 0 ≤ (h:ℝ)*batchDelays l*(2:ℝ)^(l/8) := by positivity
  linarith

end
end FiniteFourier
end LinearAlgebra
end OAI

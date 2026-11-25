import OAI.Computability.MultitapeWeakETH.Payload
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! # Retained payload length after shift and valuation losses -/

namespace OAI.Computability.MultitapeWeakETH

/-- The joint-density fourth power and the valuation penalty pay exactly
for the discarded trailing zeros. Rounding the payload down to full periods
loses fewer than two periods, including the shift. -/
theorem retained_payload {n B u s : ℕ} (hB : 0 < B) (hu : u < B)
    {γ ρ K δ q : ℝ} (hγ : 0 < γ) (hK : 0 < K)
    (density : (2:ℝ)^(-ρ*n) ≤ δ)
    (quad : δ^4*((2:ℝ)^γ)^s ≤ K*q) :
    let L := B*((n-s-u)/B)
    0 < q ∧ (γ-4*ρ)*n-2*γ*B-Real.logb 2 K ≤ γ*L+Real.logb 2 q := by
  intro L
  have hδ := (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) _).trans_le density
  have hq : 0 < q := pos_of_mul_pos_right
    ((mul_pos (pow_pos hδ _) (pow_pos (Real.rpow_pos_of_pos (by norm_num) _) _)).trans_le quad) hK.le
  have logarithm := Real.logb_le_logb_of_le (by norm_num : (1:ℝ) < 2)
    (mul_pos (pow_pos hδ _) (pow_pos (Real.rpow_pos_of_pos (by norm_num) _) _)) quad
  have initial := Real.logb_le_logb_of_le (by norm_num : (1:ℝ) < 2)
    (Real.rpow_pos_of_pos (by norm_num) _) density
  rw [Real.logb_rpow (by norm_num) (by norm_num)] at initial
  rw [Real.logb_mul (pow_pos hδ _).ne'
    (pow_pos (Real.rpow_pos_of_pos (by norm_num) _) _).ne',
    Real.logb_mul hK.ne' hq.ne',Real.logb_pow,Real.logb_pow,
    Real.logb_rpow (by norm_num) (by norm_num)] at logarithm
  have left := Nat.mod_add_div (n-s-u) B
  have remnant := Nat.mod_lt (n-s-u) hB
  have length : n ≤ L+s+2*B := by dsimp [L]; omega
  have prices := mul_le_mul_of_nonneg_left (Nat.cast_le (α := ℝ) |>.mpr length) hγ.le
  push_cast at prices
  norm_num at logarithm
  exact ⟨hq,by nlinarith only [initial,logarithm,prices]⟩

/-- Positive retained information forces a nonempty interval fitting
entirely after the valuation and shift, including for saturated subtraction. -/
theorem payload_fits {n B s u : ℕ} {q γ : ℝ} (hq : 0 < q) (hq' : q ≤ 1)
    (info : 0 < γ*(B*((n-s-u)/B):ℕ)+Real.logb 2 q) :
    let L := B*((n-s-u)/B)
    0 < L ∧ s+u+L ≤ n ∧ B ∣ L := by
  intro L
  have logq := Real.logb_le_logb_of_le (by norm_num : (1:ℝ) < 2) hq hq'
  rw [Real.logb_one] at logq
  have pos : 0 < L := by
    by_contra! h
    have zero : B*((n-s-u)/B) = 0 := Nat.eq_zero_of_le_zero h
    simp [zero,logq.not_gt] at info
  have bound : L ≤ n-s-u := by simpa only [L,Nat.mul_comm B] using Nat.div_mul_le_self (n-s-u) B
  exact ⟨pos,by omega,dvd_mul_right B _⟩

end OAI.Computability.MultitapeWeakETH

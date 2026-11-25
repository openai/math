import OAI.ThreeFlat.Diagonal.SlotEnergy
import Mathlib.Algebra.Order.Archimedean.Basic

namespace OAI
/-! # Repeated six-party shrinking followed by a port refresh -/

namespace ThreeFlat.Diagonal.SlotEnergy

/-- A fixed number of shrinking steps absorbs the multiplicative loss in
one refresh. This choice precedes the degrees used by the shrinking steps. -/
theorem exists_shrink_count {C : ℝ} (hC : 0 < C) :
    ∃ s : ℕ, 0 < s ∧ C*(126/127 : ℝ)^s ≤ 1/4 := by
  obtain ⟨n, h⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < (1/4)/C by positivity)
    (show (126/127 : ℝ) < 1 by norm_num)
  refine ⟨n+1, Nat.succ_pos _, ?_⟩
  have h' := (lt_div_iff₀ hC).mp h
  have hmono : (126/127 : ℝ)^(n+1) ≤ (126/127 : ℝ)^n := by
    rw [pow_succ]
    nlinarith [show (0:ℝ) ≤ (126/127 : ℝ)^n by positivity]
  linarith [mul_le_mul_of_nonneg_left hmono hC.le]

private theorem after_shrinks (L : ℕ → ℝ) {B : ℝ} (hB : 0 ≤ B) (s : ℕ)
    (step : ∀ i < s, L (i+1) ≤ (126/127 : ℝ)*L i + B) :
    L s ≤ (126/127 : ℝ)^s*L 0 + 127*B := by
  induction s with
  | zero => simp; linarith
  | succ s ih =>
    have h := ih (fun i hi => step i (Nat.lt_succ_of_lt hi))
    calc
      _ ≤ (126/127 : ℝ)*L s + B := step s (Nat.lt_succ_self s)
      _ ≤ (126/127 : ℝ)*((126/127 : ℝ)^s*L 0 + 127*B) + B := by linarith
      _ = _ := by rw [pow_succ]; ring

/-- Combine the individual quadratic additive errors at the beginning of
a block with the order-independent refresh constant. -/
theorem one_block_le (L : ℕ → ℝ) {C b c P final : ℝ} {s : ℕ}
    (hC : 0 ≤ C) (hb : 0 ≤ b) (hL : 0 ≤ L 0) (hsmall : C*(126/127 : ℝ)^s ≤ 1/4)
    (shrink : ∀ i < s, L (i+1) ≤ (126/127 : ℝ)*L i + b*P^2)
    (refresh : final ≤ C*L s + c*P^2) :
    final ≤ L 0 / 4 + (127*C*b+c)*P^2 := by
  have h := after_shrinks L (mul_nonneg hb (sq_nonneg P)) s shrink
  calc
    _ ≤ C*((126/127 : ℝ)^s * L 0 + 127*(b*P^2)) + c*P^2 :=
      refresh.trans (add_le_add (mul_le_mul_of_nonneg_left h hC) le_rfl)
    _ = (C*(126/127 : ℝ)^s)*L 0 + (127*C*b+c)*P^2 := by ring
    _ ≤ _ := by linarith [mul_le_mul_of_nonneg_right hsmall hL]

end ThreeFlat.Diagonal.SlotEnergy

end OAI

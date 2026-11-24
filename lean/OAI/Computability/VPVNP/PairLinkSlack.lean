import OAI.Computability.VPVNP.CursorBranchBudget

/-!
# Slack for linking a pair stage inside the live call

The enclosing control transfers add at most two external probes and
forty-seven instructions. The compression exponents leave room for those
fixed costs before the native cutoffs are applied.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CursorNetwork

open Compression Filter

theorem eventually_pairBurstSlack {C₂ : ℕ} (u : PairExponents C₂) (margin : ℕ := 2) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ)^(1/2 : ℝ) + margin ≤ (liveBucket u.δ n : ℝ) := by
  have ht : (u.θ : ℝ) < 1/100 := by simpa using (Rat.cast_lt (K := ℝ)).mpr u.theta_lt
  have hd : (u.δ : ℝ) < (u.θ : ℝ)/10 := by simpa using (Rat.cast_lt (K := ℝ)).mpr u.delta_lt
  have h := eventually_absorb_polylog ((margin : ℝ) + 1) 0 (show 1/2 < 1-(u.δ : ℝ) by linarith)
    (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [h, eventually_ge_atTop 1] with n h hn
  have h₁ := Real.one_le_rpow (show 1 ≤ (n : ℝ) by exact_mod_cast hn) (by norm_num : (0 : ℝ) ≤ 1/2)
  simp only [pow_zero,mul_one,one_mul] at h
  exact (by nlinarith only [h,mul_le_mul_of_nonneg_left h₁ (Nat.cast_nonneg (α := ℝ) margin)] :
      (n : ℝ)^(1/2 : ℝ)+margin ≤ (n : ℝ)^(1-(u.δ : ℝ))).trans
    (liveBucket_bounds (by linarith) hn).1

set_option exponentiation.threshold 10000 in
/-- Combine the metered map and cursor computation with the native setup,
slicing and traversal costs and the enclosing control transfer. -/
theorem pairTickSlack {n : ℕ} (hn : 4 ≤ n) :
    n^132 + n^500 + 47 ≤ n^9999 := by
  have h₁ := Nat.pow_le_pow_right (by omega : 0 < n) (by decide : 132 ≤ 500)
  have h₃ := (by decide : 47 ≤ 4^3).trans (Nat.pow_le_pow_left hn 3)
  have h₄ := Nat.pow_le_pow_right (by omega : 0 < n) (by decide : 3 ≤ 500)
  calc _ ≤ n^501 := by
         rw [pow_succ]
         nlinarith only [h₁,h₃.trans h₄,Nat.mul_le_mul_left (n^500) hn]
       _ ≤ n^9999 := Nat.pow_le_pow_right (by omega) (by decide)

end CursorNetwork

end VPVNP
end Computability
end OAI

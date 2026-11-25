import OAI.Computability.NearSquareRoot.CRTControlledSizes
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Pass count of the three-field XOR window -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.XorThreshold

open Controlled

/-- The three-field width costs at most two extra bits in the guard ruler. -/
theorem passes_clog {L Q : ℕ} (fit : L ≤ Q) (large : 2 ≤ Q) :
    4 + 3 * guardWidth (3 * L) ≤ 43 * Nat.clog 2 (Q+1) := by
  have padded := Nat.le_pow_clog (by decide : 1 < 2) (Q+1)
  have widen : Nat.clog 2 (3*L+1) ≤ Nat.clog 2 (Q+1) + 2 := by
    apply (Nat.clog_le_iff_le_pow (by decide)).2
    rw [pow_add]
    norm_num
    omega
  have pos := Nat.clog_pos (by decide : 1 < 2) (show 1 < Q+1 by omega)
  unfold guardWidth
  omega

theorem passes_logb {L Q : ℕ} (fit : L ≤ Q) (large : 2 ≤ Q) :
    ((4 + 3 * guardWidth (3*L) : ℕ) : ℝ) ≤ 86 * Real.logb 2 (Q+1) := by
  have scale : (2 : ℝ) ≤ Q+1 := by exact_mod_cast (show 2 ≤ Q+1 by omega)
  have one : 1 ≤ Real.logb 2 (Q+1) := by
    simpa using Real.logb_le_logb_of_le (b := (2:ℝ)) (by norm_num) (by norm_num) scale
  have c := (Nat.ceil_lt_add_one (show 0 ≤ Real.logb 2 (Q+1) by linarith)).le
  have eqn := Real.natCeil_logb_natCast 2 (Q+1)
  push_cast at eqn
  rw [eqn] at c
  have p : ((4 + 3 * guardWidth (3*L) : ℕ) : ℝ) ≤ 43 * (Nat.clog 2 (Q+1) : ℝ) := by
    exact_mod_cast passes_clog fit large
  linarith only [p,c,one]

theorem passes_log {L Q : ℕ} (fit : L ≤ Q) (large : 2 ≤ Q) :
    ((4 + 3 * guardWidth (3*L) : ℕ) : ℝ) ≤ 172 * (1 + Real.log (2 + Q)) := by
  have half : (1/2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have nonneg : 0 ≤ Real.log (2+Q) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) Q])
  have cmp := Real.log_le_log (show 0 < (Q:ℝ)+1 by positivity)
    (show (Q:ℝ)+1 ≤ 2+Q by linarith)
  have bound : Real.logb 2 (Q+1) ≤ 2 * Real.log (2+Q) := by
    rw [Real.logb,div_le_iff₀ (Real.log_pos (by norm_num))]
    nlinarith only [cmp,mul_le_mul_of_nonneg_right half nonneg]
  linarith only [passes_logb fit large,bound]

end PhysicalWalsh.XorThreshold

end NearSquareRoot
end Computability
end OAI

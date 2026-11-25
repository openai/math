import OAI.Computability.NearSquareRoot.SynchronizedPermutationBudgetNativeTick

/-! # The single native Fourier permutation pass at its selected exponent -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedLayer
open DigitPacking Filter
open SynchronizedPermutationBudget (gridVolume gridVolume_le nativeTick nativeTick_bound)
open private budget_eq volumeTerm logTerm one_le_logTerm from OAI.Computability.NearSquareRoot.FixedLayerClock

/-- The physical address permutation and sparse switch together have the
selected row exponent, with their operand frame and address logarithms included. -/
theorem nativeTick_rowClock {η : ℝ} (hr : 0 ≤ η) : RowClock η (nativeTick η) := by
  obtain ⟨C,hC,d,cost⟩ := nativeTick_bound hr
  refine ⟨C*73728,by positivity,d,?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  have vol : (gridVolume n : ℝ) ≤ 73728*((capacity n : ℝ)*addressBits n) := by
    exact_mod_cast (gridVolume_le hn).trans (Nat.mul_le_mul_left 73728 (packed_volume hn).1)
  have lg : 0 ≤ (logTerm (addressBits n))^d := pow_nonneg (zero_le_one.trans (one_le_logTerm _)) _
  rw [budget_eq]
  calc
    _ ≤ C*gridVolume n*(1+(addressBits n:ℝ))^η * (logTerm (addressBits n))^d := cost n hn
    _ ≤ C*(73728*((capacity n:ℝ)*addressBits n))*(1+(addressBits n:ℝ))^η * (logTerm (addressBits n))^d :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left vol hC) (by positivity)) lg
    _ = _ := by unfold volumeTerm; ring

end FixedLayer

end NearSquareRoot
end Computability
end OAI

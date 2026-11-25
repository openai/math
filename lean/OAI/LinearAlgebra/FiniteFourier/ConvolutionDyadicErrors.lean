import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

/-- A floor cutoff at the fourth power of the logarithmic parameter controls both dyadic errors. -/
theorem dyadicFloorErrors_le {B L C D : ℝ} (hB : 0 ≤ B) (hC : 0 < C)
    (hL : 64 * (C + 1) ≤ L) (hD : B / (4 * L) ≤ D) :
    5 * (⌊L ^ 4⌋₊ : ℝ) * (C * B / L ^ 6) ^ 2 + B ^ 2 / (⌊L ^ 4⌋₊ : ℝ) ≤ D ^ 2 / 8 := by
  have hL64 : 64 ≤ L := by linarith
  have hLpos : 0 < L := by linarith
  have hL2 : 4096 ≤ L ^ 2 := by nlinarith [mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 64) hL64]
  have hL4 : 2 ≤ L ^ 4 := by nlinarith [sq_nonneg (L ^ 2 - 1)]
  have hfloor := Nat.floor_le (show 0 ≤ L ^ 4 by positivity)
  have hhalf : L ^ 4 / 2 ≤ (⌊L ^ 4⌋₊ : ℝ) := by linarith [Nat.lt_floor_add_one (L ^ 4)]
  have hfloorpos : 0 < (⌊L ^ 4⌋₊ : ℝ) := by linarith
  have hCL : C ≤ L ^ 2 := by nlinarith [sq_nonneg (L - 1)]
  have hmain : 5 * (⌊L ^ 4⌋₊ : ℝ) * (C * B / L ^ 6) ^ 2 ≤ 5 * B ^ 2 / L ^ 4 := by
    calc
      _ ≤ 5 * L ^ 4 * (L ^ 2 * B / L ^ 6) ^ 2 := by gcongr
      _ = _ := by field_simp
  have htail : B ^ 2 / (⌊L ^ 4⌋₊ : ℝ) ≤ 2 * B ^ 2 / L ^ 4 := by
    calc
      _ ≤ B ^ 2 / (L ^ 4 / 2) := by gcongr
      _ = _ := by ring
  have hshrink : 7 / L ^ 4 ≤ 1 / (128 * L ^ 2) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith [mul_nonneg (sq_nonneg L) (show 0 ≤ L ^ 2 - 896 by linarith)]
  calc
    _ ≤ 5 * B ^ 2 / L ^ 4 + 2 * B ^ 2 / L ^ 4 := add_le_add hmain htail
    _ = B ^ 2 * (7 / L ^ 4) := by ring
    _ ≤ B ^ 2 * (1 / (128 * L ^ 2)) := by gcongr
    _ = (B / (4 * L)) ^ 2 / 8 := by ring
    _ ≤ _ := by gcongr

end FiniteFourier
end LinearAlgebra
end OAI

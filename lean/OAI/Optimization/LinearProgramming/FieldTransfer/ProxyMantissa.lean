import OAI.Optimization.LinearProgramming.Compression.ProxySeries

/-! The dyadic output of the two truncated real series in §§3.4 and 8. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace FieldTransfer
namespace RealProxy

open OAI.Optimization.LinearProgramming.Compression (logTruncation dyadicSearch dyadicTest dyadicSearch_brackets
  mantissaGridNumerator mantissaGrid_cost abs_logb_sub_truncation_ratio two_thirds_le_logTruncation_two)
open scoped BigOperators

private theorem ratio_bounds {z : ℝ} (hz : 1 ≤ z) (hz' : z ≤ 2) {M : Nat} (hM : 1 ≤ M) :
    0 ≤ logTruncation z M / logTruncation 2 M ∧ logTruncation z M / logTruncation 2 M ≤ 1 := by
  have hd := two_thirds_le_logTruncation_two hM
  have hp : 0 < logTruncation (2:ℝ) M := by linarith
  have hx : 0 ≤ (z - 1) / (z + 1) := div_nonneg (by linarith) (by linarith)
  have hx' : (z - 1) / (z + 1) ≤ ((2:ℝ)-1)/(2+1) := by
    apply (div_le_iff₀ (by linarith : 0 < z+1)).2
    linarith
  constructor
  · apply div_nonneg _ hp.le
    exact mul_nonneg (by norm_num) <| Finset.sum_nonneg fun i _ =>
      div_nonneg (pow_nonneg hx _) (by positivity)
  · apply (div_le_one hp).2
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Finset.sum_le_sum
    exact fun i _ => div_le_div_of_nonneg_right (pow_le_pow_left₀ hx hx' _) (by positivity)

/-- The small-regime dyadic numerator uses the emitted bits of comparisons. The bound is
uniform for all real mantissas in the closed interval, including hardware-exact ties. -/
theorem mantissaGrid_error {z : ℝ} (hz : 1 ≤ z) (hz' : z ≤ 2) (k : ℕ) :
    |((mantissaGridNumerator z k).1 : ℝ)/2^(k+2) - Real.logb 2 z| < (1/2 : ℝ)^k/2 := by
  let s := logTruncation z (k+6)/logTruncation 2 (k+6)
  let p := (mantissaGridNumerator z k).1
  let d := (2:ℝ)^(k+2)
  have hd : 0 < d := by positivity
  obtain ⟨hs, hsu⟩ := ratio_bounds hz hz' (M := k+6) (by omega)
  obtain ⟨hl, hu⟩ := dyadicSearch_brackets hs hsu (k+2)
  change (p:ℝ) ≤ d*s at hl
  change d*s ≤ (p:ℝ)+1 at hu
  have hg : |(p:ℝ)/d - s| ≤ 1/d := by
    have lo : (p:ℝ)/d ≤ s := (div_le_iff₀ hd).2 (mul_comm d s ▸ hl)
    rw [abs_of_nonpos (sub_nonpos.mpr lo), show -((p:ℝ)/d - s) = (d*s-p)/d by field_simp; ring,
      div_le_div_iff_of_pos_right hd]
    linarith
  have he := abs_logb_sub_truncation_ratio hz hz' (M := k+6) (by omega)
  have hd' : 1/d = (1/2:ℝ)^k/4 := by dsimp [d]; rw [pow_add,one_div_pow]; ring
  have hk : 0 < (1/2:ℝ)^k := by positivity
  have herr : |s - Real.logb 2 z| < (1/2:ℝ)^k / 4 := by
    rw [pow_add] at he
    norm_num at he
    change |logTruncation z _ / logTruncation 2 _ - _| < _
    linarith
  change |(p:ℝ)/d - Real.logb 2 z| < _
  calc
    _ ≤ |(p:ℝ)/d - s| + |s-Real.logb 2 z| := abs_sub_le _ _ _
    _ < 1/d + (1/2:ℝ)^k/4 := add_lt_add_of_le_of_lt hg herr
    _ = _ := by rw [hd']; ring

end RealProxy
end FieldTransfer
end LinearProgramming
end Optimization
end OAI

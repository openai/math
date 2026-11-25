import OAI.LinearAlgebra.FiniteFourier.ExtensionCost
import OAI.LinearAlgebra.FiniteFourier.ConvolutionBound

/-! # Uniform cost bound for power-basis multiplication

The precision-doubling call increases the logarithmic factor by at most
`2 ^ β ≤ 2`. Together with the two original-precision calls and the final
subtractions this gives the constant `6 * C + 1`.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

/-- Real bound on the combined gate budgets for the three convolutions and
coordinate subtractions at any positive extension degree. -/
theorem powerBasis_budget_le {β C : ℝ} (hβ : 0 ≤ β) (hβ₁ : β ≤ 1) (hC : 0 ≤ C)
    {e : ℕ} (he : 0 < e) :
    ((convolutionBudget β C (2 * e) + 2 * convolutionBudget β C e + e : ℕ) : ℝ) ≤
      (6 * C + 1) * e * (1 + Real.logb 2 e) ^ β := by
  have he₁ : (1 : ℝ) ≤ e := by exact_mod_cast he
  have he₀ : 0 < (e : ℝ) := by exact_mod_cast he
  have hlog : 0 ≤ Real.logb 2 e := Real.logb_nonneg (by norm_num) he₁
  have hpow := Real.one_le_rpow (show 1 ≤ 1 + Real.logb 2 e by linarith) hβ
  have htwo : (2 : ℝ) ^ β ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hβ₁
  have hdr : (1 + Real.logb 2 (2 * (e : ℝ))) ^ β ≤ 2 * (1 + Real.logb 2 e) ^ β := by
    rw [Real.logb_mul (by norm_num) he₀.ne']
    have hbase : Real.logb 2 2 = 1 := by norm_num [Real.logb]
    rw [hbase]
    calc
      _ ≤ (2 * (1 + Real.logb 2 e)) ^ β :=
        Real.rpow_le_rpow (by linarith) (by linarith) hβ
      _ = (2 : ℝ) ^ β * (1 + Real.logb 2 e) ^ β :=
        Real.mul_rpow (by norm_num) (by linarith)
      _ ≤ _ := mul_le_mul_of_nonneg_right htwo (by linarith)
  have hsmall := convolutionBudget_le (β := β) hC he
  have hlarge := convolutionBudget_le (β := β) hC (show 0 < 2 * e by omega)
  push_cast at hlarge ⊢
  have hdouble := mul_le_mul_of_nonneg_left hdr (show 0 ≤ C * (2 * (e : ℝ)) by positivity)
  have hadd := mul_le_mul_of_nonneg_left hpow he₀.le
  linarith

/-- Multiplication by a prescribed extension scalar has the uniform real gate
bound for every power basis of dimension `e`. -/
theorem FixedConvolutionBound.powerBasis_scalar {K E : Type*} [Field K] [Field E] [Algebra K E]
    {β C : ℝ} (h : FixedConvolutionBound K β C) (hβ : 0 ≤ β) (hβ₁ : β ≤ 1) (hC : 0 ≤ C)
    (pb : PowerBasis K E) (u : E) :
    (complexity (fun i j => pb.basis.repr (u * pb.basis j) i) : ℝ) ≤
      (6 * C + 1) * pb.dim * (1 + Real.logb 2 pb.dim) ^ β := by
  refine le_trans ?_ (powerBasis_budget_le hβ hβ₁ hC pb.dim_pos)
  exact_mod_cast (complexity_le_iff ..).mpr
    (realizable_powerBasis_scalar _ h.realizable pb u)

end FiniteFourier
end LinearAlgebra
end OAI

import OAI.LinearAlgebra.FiniteFourier.RankSpecialization
import OAI.LinearAlgebra.FiniteFourier.RationalCoefficientInterpolation
import OAI.LinearAlgebra.FiniteFourier.WeightedCoefficients

/-! # Weighted coefficients of the rank correction

The rank constraint is imposed on the matrix over the rational function field. After taking
a tensor power, interpolation expresses any Taylor coefficient as a sum of at most `ek+1`
scalar multiples of powers of regular evaluations.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Polynomial
open scoped BigOperators

noncomputable section

variable {K μ ι : Type*} [Field K] [Fintype μ] [Fintype ι]

/-- The power series assigned to the output–input pair of a common-denominator matrix. -/
def quotientSeries (P : Matrix μ ι K[X]) (h : K[X]) (z : μ × ι) : PowerSeries K :=
  (P z.1 z.2 : PowerSeries K) * (h : PowerSeries K)⁻¹

/-- The estimate (Rcoeff), with the manuscript's explicit linear count of evaluations. -/
theorem rationalPowerCoefficient_price_le [Infinite K] (ν : TensorValue K (μ × ι))
    (P : Matrix μ ι K[X]) (h : K[X]) (h0 : h.coeff 0 ≠ 0)
    (e r : ℕ) (he : ∀ u v, (P u v).natDegree ≤ e) (hr : (rationalQuotient P h).rank ≤ r)
    {w U : ℝ} (hw : 0 ≤ w) (hw1 : w ≤ 1)
    (hrank : ∀ M : Matrix μ ι K, M.rank ≤ r →
      ν.price 1 (slotPower (Function.uncurry M) 1) ≤ U) (k i : ℕ) :
    w ^ i * ν.price k (powerCoeff (quotientSeries P h) k i) ≤ (e * (k : ℝ) + 1) * U ^ k := by
  classical
  obtain ⟨t, ht, a, ha⟩ := exists_rationalPowerCoefficient_weights h h0 (Function.uncurry P) e
    (fun z ↦ he z.1 z.2) k
  let v (j : Fin (e*k+1)) := Function.uncurry (quotientAt P h (t j))
  have hcoeff : powerCoeff (quotientSeries P h) k i = ∑ j, a i j • slotPower (v j) k := by
    funext x
    simpa only [powerCoeff, quotientSeries, slotPower, v, quotientAt, Function.uncurry, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using ha i x
  have h1 (j : Fin (e*k+1)) := hrank (quotientAt P h (t j)) ((rank_quotientAt_le P h _ (ht j)).trans hr)
  calc
    _ ≤ ν.price k (powerCoeff (quotientSeries P h) k i) :=
      mul_le_of_le_one_left (ν.nonneg _) (pow_le_one₀ hw hw1)
    _ ≤ ∑ j, ν.price k (a i j • slotPower (v j) k) := hcoeff ▸ ν.price_sum _ _
    _ ≤ ∑ _ : Fin (e*k+1), U ^ k := by
      refine Finset.sum_le_sum fun j _ ↦ (ν.scale _ _).trans ?_
      rw [ν.power]
      exact pow_le_pow_left₀ (ν.nonneg _) (h1 j) k
    _ = _ := by simp

/-- A rational correction of generic rank at most `r` satisfies the polynomial-overhead
weighted bound whenever every one-slot rank-`r` matrix has value at most `U`. -/
theorem weightedBound_rationalQuotient [Infinite K] (ν : TensorValue K (μ × ι))
    (P : Matrix μ ι K[X]) (h : K[X]) (h0 : h.coeff 0 ≠ 0)
    (e r : ℕ) (he : ∀ u v, (P u v).natDegree ≤ e) (hr : (rationalQuotient P h).rank ≤ r)
    {w U : ℝ} (hw : 0 ≤ w) (hw1 : w ≤ 1) (hU : 0 ≤ U)
    (hrank : ∀ M : Matrix μ ι K, M.rank ≤ r →
      ν.price 1 (slotPower (Function.uncurry M) 1) ≤ U) :
    WeightedBound ν w U (quotientSeries P h) := by
  refine ⟨e, fun k i ↦ (rationalPowerCoefficient_price_le ν P h h0 e r he hr hw hw1 hrank k i).trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg hU _)
  calc
    (e : ℝ) * k + 1 = k * e + 1 := by ring
    _ ≤ ((k : ℝ) + 1) ^ e := Real.mul_add_one_le_add_one_pow (Nat.cast_nonneg k) e
    _ ≤ _ := pow_le_pow_left₀ (by positivity) (by linarith [Nat.cast_nonneg (α := ℝ) i]) e

end

end FiniteFourier
end LinearAlgebra
end OAI

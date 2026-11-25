import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Bounded range reduction by repeated squaring and greedy binary descent in §3.4. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace FieldTransfer
namespace RealProxy

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- A small result records the integer exponent and its actual field power.
The counter includes both the upward and the downward comparisons. -/
structure PowerSearchResult (K : Type*) where
  answer : Option (ℕ × K)
  comparisons : ℕ

/-- First square until finding a strict upper bound or reaching the threshold.
On the return path, use the powers already constructed to recover all exponent bits. -/
def powerSearch : ℕ → K → K → PowerSearchResult K
  | 0, z, p =>
      if z < p then ⟨some (0, 1), 1⟩ else ⟨none, 1⟩
  | fuel + 1, z, p =>
      if z < p then ⟨some (0, 1), 1⟩ else
        let ret := powerSearch fuel z (p * p)
        match ret.answer with
        | none => ⟨none, ret.comparisons + 1⟩
        | some (e, q) =>
          let next := q * p
          if z < next then ⟨some (2 * e, q), ret.comparisons + 2⟩
          else ⟨some (2 * e + 1, next), ret.comparisons + 2⟩

/-- A small answer is an exact exponent bracket. Saturation means the largest prescribed
power was actually reached. No comparison against that potentially enormous power is
performed on the branch that stops early. -/
theorem powerSearch_spec (fuel : ℕ) (z p : K) (hz : 1 ≤ z) (hp : 1 < p) :
    (powerSearch fuel z p).comparisons ≤ 2 * fuel + 1 ∧
    (match (powerSearch fuel z p).answer with
     | none => p ^ (2 ^ fuel) ≤ z
     | some (e, q) => q = p ^ e ∧ q ≤ z ∧ z < q * p ∧ e < 2 ^ fuel) := by
  induction fuel generalizing p with
  | zero =>
    by_cases h : z < p
    · simpa [powerSearch, h] using (show 1 ≤ z ∧ z < p from ⟨hz, h⟩)
    · simp [powerSearch, h, le_of_not_gt h]
  | succ n ih =>
    by_cases h : z < p
    · simp [powerSearch, h, hz]
    · have hsq : 1 < p * p := by nlinarith [sq_nonneg (p-1)]
      have hrec := ih (p * p) hsq
      have hpow (k : ℕ) : (p * p) ^ k = p ^ (2 * k) := by
        rw [← sq, pow_mul]
      cases hr : powerSearch n z (p * p) with
      | mk answer cost =>
        rw [hr] at hrec
        obtain ⟨hc, ho⟩ := hrec
        change cost ≤ 2 * n + 1 at hc
        cases answer with
        | none =>
          change (p * p) ^ (2 ^ n) ≤ z at ho
          rw [hpow, ← Nat.pow_succ'] at ho
          simpa [powerSearch, h, hr, ho] using (show cost + 1 ≤ 2 * (n + 1) + 1 by omega)
        | some pair =>
          rcases pair with ⟨e, q⟩
          change q = (p*p)^e ∧ q ≤ z ∧ z < q*(p*p) ∧ e < 2^n at ho
          obtain ⟨hq, hqz, hzq, he⟩ := ho
          rw [hpow] at hq
          have hcost : cost + 2 ≤ 2 * (n+1) + 1 := by omega
          by_cases ht : z < q * p
          · have he' : 2 * e < 2 ^ (n+1) := by rw [Nat.pow_succ']; omega
            simp only [powerSearch, ite_eq_right h, hr, ite_eq_left ht]
            exact ⟨hcost, hq, hqz, ht, he'⟩
          · have hn : q * p ≤ z := le_of_not_gt ht
            have hzq' : z < q * p * p := by simpa [mul_assoc] using hzq
            have hq' : q * p = p ^ (2 * e + 1) := by rw [hq, pow_succ]
            have he' : 2 * e + 1 < 2 ^ (n+1) := by rw [Nat.pow_succ']; omega
            simp only [powerSearch, ite_eq_right h, hr, ite_eq_right ht]
            exact ⟨hcost, hq', hn, hzq', he'⟩

/-- The single reciprocal normalizes a positive magnitude to the interval `[1,∞)`. -/
def normalizedMagnitude (mag : K) : K := if mag < 1 then mag⁻¹ else mag

theorem one_le_normalizedMagnitude {mag : K} (h : 0 < mag) : 1 ≤ normalizedMagnitude mag := by
  by_cases hm : mag < 1
  · simpa [normalizedMagnitude, hm] using (one_le_inv₀ h).mpr hm.le
  · simpa [normalizedMagnitude, hm] using le_of_not_gt hm

/-- Squaring and inversion interpret the same threshold comparison over genuine real coefficients. -/
theorem logb_normalizedMagnitude {mag : ℝ} (h : 0 < mag) :
    Real.logb 2 (normalizedMagnitude mag) = |Real.logb 2 mag| := by
  by_cases hm : mag < 1
  · have hneg := (Real.logb_neg_iff (by norm_num : (1:ℝ) < 2) h).mpr hm
    simp [normalizedMagnitude, hm, abs_of_neg hneg]
  · have hn := Real.logb_nonneg (by norm_num : (1:ℝ) < 2) (le_of_not_gt hm)
    simp [normalizedMagnitude, hm, abs_of_nonneg hn]

theorem powerSearch_saturates_iff (fuel : ℕ) {mag : ℝ} (hm : 0 < mag) :
    (powerSearch fuel (normalizedMagnitude mag) 2).answer = none ↔
      (2:ℝ)^fuel ≤ |Real.logb 2 mag| := by
  let z := normalizedMagnitude mag
  have hz : 1 ≤ z := one_le_normalizedMagnitude hm
  have hc : (2:ℝ)^(2^fuel : ℕ) ≤ z ↔ (2:ℝ)^fuel ≤ Real.logb 2 z := by
    have he := Real.logb_le_logb (by norm_num : (1:ℝ)<2)
      (x := (2:ℝ)^(2^fuel :ℕ)) (by positivity) (zero_lt_one.trans_le hz)
    simpa [Real.logb_pow] using he.symm
  rw [← logb_normalizedMagnitude hm]
  change (powerSearch fuel z 2).answer = none ↔ _
  rw [← hc]
  have hs := (powerSearch_spec fuel z 2 hz (by norm_num)).2
  cases hv : (powerSearch fuel z 2).answer with
  | none => simpa [hv] using hs
  | some pr =>
    rcases pr with ⟨e,q⟩
    simp only [hv] at hs
    obtain ⟨rfl, _, hu, he⟩ := hs
    have hl : (2:ℝ)^(e+1) ≤ 2^(2^fuel) := pow_le_pow_right₀ (by norm_num) he
    rw [←pow_succ] at hu
    simp [not_le.mpr (hu.trans_le hl)]

theorem powerSearch_mantissa (fuel : ℕ) {mag : ℝ} (hm : 0 < mag) {e : ℕ} {q : ℝ}
    (h : (powerSearch fuel (normalizedMagnitude mag) 2).answer = some (e,q)) :
    1 ≤ normalizedMagnitude mag / q ∧ normalizedMagnitude mag / q < 2 ∧
      |Real.logb 2 mag| = e + Real.logb 2 (normalizedMagnitude mag / q) := by
  let z := normalizedMagnitude mag
  have hz : 1 ≤ z := one_le_normalizedMagnitude hm
  have hs := (powerSearch_spec fuel z 2 hz (by norm_num)).2
  change (powerSearch fuel z 2).answer = _ at h
  rw [h] at hs
  obtain ⟨rfl,hl,hu,_⟩ := hs
  have hp : (0:ℝ) < 2^e := by positivity
  refine ⟨(one_le_div hp).mpr hl, (div_lt_iff₀ hp).mpr (by simpa [mul_comm] using hu), ?_⟩
  rw [← logb_normalizedMagnitude hm]
  change Real.logb 2 z = _
  rw [Real.logb_div (zero_lt_one.trans_le hz).ne' hp.ne', Real.logb_pow,
    Real.logb_self_eq_one (by norm_num), mul_one]
  ring

end RealProxy
end FieldTransfer
end LinearProgramming
end Optimization
end OAI

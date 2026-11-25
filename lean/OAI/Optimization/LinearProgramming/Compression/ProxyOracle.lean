import OAI.Optimization.LinearProgramming.Compression.Proxy
import OAI.Optimization.LinearProgramming.Compression.ProxyRange
import OAI.Optimization.LinearProgramming.Compression.ProxySeries

/-! Rational construction and exact affine comparisons of the logarithm proxies of §3.4. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open scoped BigOperators

/-- A small logarithm is stored in units of `1 / 2^(k+2)`. A large logarithm is left
symbolic. The choice and the grid value depend only on the magnitude and the precisions,
so repeated sign queries refer to the same proxy. -/
def logProxyNumerator (fuel k : ℕ) (mag : ℚ) : Option ℤ :=
  let z := normalizedMagnitude mag
  match (powerSearch fuel z 2).answer with
  | none => none
  | some (e, q) =>
    let digit := (mantissaGridNumerator (z / q) k).1
    let numerator : ℕ := 2 ^ (k+2) * e + digit
    some (if mag < 1 then -(numerator : ℤ) else (numerator : ℤ))

/-- The real number denoted by the symbolic or explicitly gridded representation. -/
noncomputable def logProxyValue (k : ℕ) (mag : ℚ) : Option ℤ → ℝ
  | none => Real.logb 2 mag
  | some u => (u : ℝ) / (2 : ℝ) ^ (k + 2)

private theorem logProxyNumerator_of_some (fuel k : ℕ) (mag : ℚ) (e : ℕ) (q : ℚ)
    (h : (powerSearch fuel (normalizedMagnitude mag) 2).answer = some (e,q)) :
    logProxyNumerator fuel k mag =
    some (if mag < 1 then
        -((2 ^ (k+2) * e + (mantissaGridNumerator (normalizedMagnitude mag / q) k).1 : ℕ) : ℤ)
      else ((2 ^ (k+2) * e + (mantissaGridNumerator (normalizedMagnitude mag / q) k).1 : ℕ) : ℤ)) := by
  simp only [logProxyNumerator, h]

theorem logProxyNumerator_eq_none_iff (fuel k : ℕ) {mag : ℚ} (hm : 0 < mag) :
    logProxyNumerator fuel k mag = none ↔
    (2 : ℝ) ^ fuel ≤ |Real.logb 2 (mag : ℝ)| := by
  rw [← powerSearch_saturates_iff fuel hm]
  unfold logProxyNumerator
  cases h : (powerSearch fuel (normalizedMagnitude mag) 2).answer with
  | none => simp [h]
  | some pair => cases pair; simp [h]

/-- After restoring the integer part and sign, every resulting proxy has error less than
half the target tolerance. This covers magnitudes both above and below one. -/
theorem logProxyValue_error (fuel k : ℕ) {mag : ℚ} (hm : 0 < mag) :
    |logProxyValue k mag (logProxyNumerator fuel k mag) - Real.logb 2 (mag : ℝ)| <
      (1 / 2 : ℝ) ^ k / 2 := by
  let z := normalizedMagnitude mag
  have hm' : (0 : ℝ) < mag := by exact_mod_cast hm
  cases hs : (powerSearch fuel z 2).answer with
  | none =>
    simp only [logProxyNumerator, ← show z = normalizedMagnitude mag from rfl, hs,
      logProxyValue, sub_self, abs_zero]
    positivity
  | some pair =>
    rcases pair with ⟨e,q⟩
    obtain ⟨hl, hu, he⟩ := powerSearch_mantissa fuel hm hs
    change |Real.logb 2 (mag : ℝ)| = (e : ℝ) + Real.logb 2 ((z / q : ℚ) : ℝ) at he
    let n := (mantissaGridNumerator (z / q) k).1
    let u := 2 ^ (k+2) * e + n
    have hfrac : (u : ℝ) / (2 : ℝ) ^ (k+2) = (e : ℝ) + (n : ℝ) / (2 : ℝ) ^ (k+2) := by
      dsimp [u]
      push_cast
      field_simp
    have hg := mantissaGrid_error hl hu.le k
    change |(n : ℝ) / (2 : ℝ) ^ (k + 2) - Real.logb 2 ((z / q : ℚ) : ℝ)| < _ at hg
    have habs :
        |(u : ℝ) / (2 : ℝ) ^ (k+2) - abs (Real.logb 2 (mag : ℝ))| <
          (1/2 : ℝ)^k / 2 := by
      rw [hfrac, he, add_sub_add_left_eq_sub]
      exact hg
    rw [logProxyNumerator_of_some fuel k mag e q hs]
    by_cases hm1 : mag < 1
    · have hneg : Real.logb 2 (mag : ℝ) < 0 :=
        (Real.logb_neg_iff (by norm_num) hm').mpr (by exact_mod_cast hm1)
      rw [abs_of_neg hneg] at habs
      simp only [ite_eq_left hm1, logProxyValue, Int.cast_neg, Int.cast_natCast]
      change |-(u : ℝ) / (2 : ℝ) ^ (k+2) - Real.logb 2 (mag : ℝ)| < _
      rw [show -(u : ℝ) / (2 : ℝ) ^ (k+2) - Real.logb 2 (mag : ℝ) =
        -((u : ℝ) / (2 : ℝ) ^ (k+2) + Real.logb 2 (mag : ℝ)) by ring, abs_neg]
      simpa [sub_neg_eq_add] using habs
    · have hpos := (Real.logb_nonneg_iff (by norm_num : (1 : ℝ) < 2) hm').mpr
        (by exact_mod_cast le_of_not_gt hm1)
      rw [abs_of_nonneg hpos] at habs
      simpa only [ite_eq_right hm1, logProxyValue, Int.cast_natCast] using habs

/-- The numerator of an explicitly gridded proxy grows only with the prescribed parameters. -/
theorem logProxyNumerator_abs_lt (fuel k : ℕ) {mag : ℚ} (hm : 0 < mag) {u : ℤ}
    (h : logProxyNumerator fuel k mag = some u) :
    |u| < (2 : ℤ) ^ (k+2) * 2 ^ fuel := by
  let z := normalizedMagnitude mag
  have hs := (powerSearch_spec fuel z 2 (one_le_normalizedMagnitude hm) (by norm_num)).2
  cases ht : (powerSearch fuel z 2).answer with
  | none =>
    have hs0 : logProxyNumerator fuel k mag = none := by
      simp only [logProxyNumerator, ← show z = normalizedMagnitude mag from rfl, ht]
    rw [hs0] at h
    contradiction
  | some pair =>
    rcases pair with ⟨e,q⟩
    rw [ht] at hs
    obtain ⟨_, _, _, he⟩ := hs
    have hn := (mantissaGrid_cost (z / q) k).2
    let n := (mantissaGridNumerator (z / q) k).1
    have hbound : 2^(k+2) * e + n < 2^(k+2) * 2^fuel := calc
      _ < 2^(k+2) * e + 2^(k+2) := Nat.add_lt_add_left hn _
      _ = 2^(k+2) * (e+1) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ he
    rw [logProxyNumerator_of_some fuel k mag e q ht] at h
    simp only [Option.some.injEq] at h
    subst u
    by_cases hm1 : mag < 1
    · simp only [ite_eq_left hm1, abs_neg, abs_of_nonneg (Int.natCast_nonneg _)]
      exact_mod_cast hbound
    · simp only [ite_eq_right hm1, abs_of_nonneg (Int.natCast_nonneg _)]
      exact_mod_cast hbound

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Sign query computed from positive rational minor magnitudes, by gridding small logs,
retaining large ones symbolically, and applying the rational product comparison. -/
def logProxySign (fuel k : ℕ) (c : ℤ) (a : ι → ℤ) (mag : ι → ℚ) : Ordering :=
  let data i := logProxyNumerator fuel k (mag i)
  let large := Finset.univ.filter (fun i => data i = none)
  compareProxyAffine large (2 ^ (k+2)) c a (fun i => (data i).getD 0) mag

/-- The mixed rational/symbolic expression uses exactly the fixed proxy chosen for
each magnitude, independently of the affine coefficients. -/
theorem logProxyAffine_eq (fuel k : ℕ) (c : ℤ) (a : ι → ℤ) (mag : ι → ℚ) :
    let data i := logProxyNumerator fuel k (mag i)
    let large := Finset.univ.filter (fun i => data i = none)
    proxyAffine large (2 ^ (k+2)) c a (fun i => (data i).getD 0) mag =
      (c : ℝ) + ∑ i, (a i : ℝ) * logProxyValue k (mag i) (data i) := by
  let data i := logProxyNumerator fuel k (mag i)
  let large := Finset.univ.filter (fun i => data i = none)
  change proxyAffine large (2 ^ (k+2)) c a (fun i => (data i).getD 0) mag = _
  unfold proxyAffine
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  change _ = (a i : ℝ) * logProxyValue k (mag i) (data i)
  cases hi : data i <;> simp [large, hi, logProxyValue]

/-- The algorithm evaluates every integer affine form against a single collection of
proxies, with zero, positive and negative answers all preserved exactly. -/
theorem logProxySign_correct (fuel k : ℕ) (c : ℤ) (a : ι → ℤ) (mag : ι → ℚ)
    (hm : ∀ i, 0 < mag i) :
    let value i := logProxyValue k (mag i) (logProxyNumerator fuel k (mag i))
    let form : ℝ := c + ∑ i, (a i : ℝ) * value i
    logProxySign fuel k c a mag = if form < 0 then .lt else if 0 < form then .gt else .eq := by
  let data i := logProxyNumerator fuel k (mag i)
  let large := Finset.univ.filter (fun i => data i = none)
  have hc := compareProxyAffine_correct large (2^(k+2)) (by positivity) c a
    (fun i => (data i).getD 0) mag (fun i _ => hm i)
  rw [logProxyAffine_eq fuel k c a mag] at hc
  exact hc

end Compression
end LinearProgramming
end Optimization
end OAI

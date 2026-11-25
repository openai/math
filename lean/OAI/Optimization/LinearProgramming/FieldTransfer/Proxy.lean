import OAI.Optimization.LinearProgramming.FieldTransfer.ProxyRange
import OAI.Optimization.LinearProgramming.FieldTransfer.ProxySign
import OAI.Optimization.LinearProgramming.FieldTransfer.ProxyMantissa

/-! The real-input sign oracle in §§3.4 and 8. The construction produces explicit dyadic
digits for bounded minor logarithms. The logarithm in `denote` appears only in its specification. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace FieldTransfer
namespace RealProxy

open OAI.Optimization.LinearProgramming.Compression (logTruncation dyadicSearch dyadicTest dyadicSearch_brackets
  mantissaGridNumerator mantissaGrid_cost abs_logb_sub_truncation_ratio two_thirds_le_logTruncation_two)
open scoped BigOperators

noncomputable def numerator (fuel k : Nat) (mag : ℝ) : Option ℤ :=
  let z := normalizedMagnitude mag
  match (powerSearch fuel z 2).answer with
  | none => none
  | some (e,q) =>
    let digit := (mantissaGridNumerator (z/q) k).1
    let n := 2^(k+2)*e+digit
    some (if mag < 1 then -(n:ℤ) else (n:ℤ))

noncomputable def denote (k : Nat) (mag : ℝ) : Option ℤ → ℝ
  | none => Real.logb 2 mag
  | some g => (g:ℝ)/(2:ℝ)^(k+2)

theorem numerator_eq_none_iff (fuel k : Nat) {mag : ℝ} (hm : 0 < mag) :
    numerator fuel k mag = none ↔ (2:ℝ)^fuel ≤ |Real.logb 2 mag| := by
  rw [← powerSearch_saturates_iff fuel hm]
  unfold numerator
  cases h : (powerSearch fuel (normalizedMagnitude mag) 2).answer with
  | none => simp [h]
  | some a => cases a; simp [h]

theorem proxy_error (fuel k : Nat) {mag : ℝ} (hm : 0 < mag) :
    |denote k mag (numerator fuel k mag) - Real.logb 2 mag| < (1/2:ℝ)^k/2 := by
  let z := normalizedMagnitude mag
  cases hs : (powerSearch fuel z 2).answer with
  | none =>
    simp only [numerator, ← show z = normalizedMagnitude mag from rfl, hs, denote,
      sub_self, abs_zero]
    positivity
  | some pair =>
    rcases pair with ⟨e,q⟩
    obtain ⟨hl, hu, he⟩ := powerSearch_mantissa fuel hm hs
    let digit := (mantissaGridNumerator (z/q) k).1
    let n := 2^(k+2)*e+digit
    have heq : (n:ℝ)/(2:ℝ)^(k+2) = e + (digit:ℝ)/(2:ℝ)^(k+2) := by
      dsimp only [n]
      push_cast
      field_simp
    have hbound : |(n:ℝ)/(2:ℝ)^(k+2) - abs (Real.logb 2 mag)| < (1/2:ℝ)^k/2 := by
      rw [heq, he, add_sub_add_left_eq_sub]
      exact mantissaGrid_error hl hu.le k
    unfold numerator
    change |denote k mag (match (powerSearch fuel z 2).answer with
      | none => none | some (a,b) => some (if mag < 1 then
        -(↑(2^(k+2)*a+(mantissaGridNumerator (z/b) k).1):ℤ) else ↑(2^(k+2)*a+(mantissaGridNumerator (z/b) k).1))) - _| < _
    rw [hs]
    by_cases h : mag < 1
    · have hlog := (Real.logb_neg_iff (by norm_num : (1:ℝ)<2) hm).mpr h
      rw [abs_of_neg hlog] at hbound
      simp only [ite_eq_left h, denote, Int.cast_neg, Int.cast_natCast]
      change |-(n:ℝ)/2^(k+2) - _| < _
      rw [show -(n:ℝ)/2^(k+2) - Real.logb 2 mag = -((n:ℝ)/2^(k+2) + Real.logb 2 mag) by ring,
        abs_neg]
      simpa [sub_neg_eq_add] using hbound
    · have hlog := Real.logb_nonneg (by norm_num : (1:ℝ)<2) (le_of_not_gt h)
      rw [abs_of_nonneg hlog] at hbound
      simpa only [ite_eq_right h, denote, Int.cast_natCast] using hbound

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def proxySign (fuel k : Nat) (c : ℤ) (a : ι → ℤ) (mag : ι → ℝ) : Ordering :=
  let digits i := numerator fuel k (mag i)
  let large := Finset.univ.filter (fun i => digits i = none)
  compareAffine large (2^(k+2)) c a (fun i => (digits i).getD 0) mag

/-- Every affine query uses a single consistent family of real proxies,
whose explicit rationals or original symbolic magnitudes depend only on the minor index. -/
theorem proxySign_correct (fuel k : Nat) (c : ℤ) (a : ι → ℤ) (mag : ι → ℝ) (hm : ∀ i, 0 < mag i) :
    let form : ℝ := c + ∑ i, (a i : ℝ) * denote k (mag i) (numerator fuel k (mag i))
    proxySign fuel k c a mag = if form < 0 then .lt else if 0 < form then .gt else .eq := by
  let digits i := numerator fuel k (mag i)
  let large := Finset.univ.filter (fun i => digits i = none)
  have he : affineLog large (2^(k+2)) c a (fun i => (digits i).getD 0) mag =
      (c:ℝ) + ∑ i, (a i : ℝ) * denote k (mag i) (digits i) := by
    unfold affineLog
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    cases hd : digits i <;> simp [large, hd, denote]
  exact he ▸ compareAffine_correct large (2^(k+2)) (by positivity) c a
    (fun i => (digits i).getD 0) mag (fun i _ => hm i)

end RealProxy
end FieldTransfer
end LinearProgramming
end Optimization
end OAI

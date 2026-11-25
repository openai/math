import OAI.Optimization.LinearProgramming.Compression.ProxyCost

/-! The rational powers that actually occur in the bounded range search have small encodings,
including the first upper bound and the rejected trials in the downward binary search. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open OAI.Optimization.LinearProgramming.RAM

/-- The upward current powers and the downward trial products, in evaluation order. -/
def powerSearchOperands : ℕ → ℚ → ℚ → List ℚ
  | 0, _, p => [p]
  | n+1, z, p =>
    if z < p then [p] else
      p :: (powerSearchOperands n z (p*p) ++
        (match (powerSearch n z (p*p)).answer with
         | none => []
         | some (_,q) => [q*p]))

theorem exponent_le_ratBits {mag : ℚ} (hm : 0 < mag) {e : ℕ}
    (h : (2 : ℚ)^e ≤ normalizedMagnitude mag) : e ≤ ratBits mag := by
  have hu : (2 : ℝ)^e ≤ (normalizedMagnitude mag : ℝ) := by exact_mod_cast h
  have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity) hu
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one, logb_normalizedMagnitude hm] at hl
  have h' := hl.trans (abs_logb_le_rat_bits hm)
  have hn : e ≤ mag.num.natAbs.size + mag.den.size := by exact_mod_cast h'
  exact hn.trans (magnitude_size_le_ratBits mag)

private theorem operands_exponents (fuel : ℕ) (mag : ℚ) (hm : 0 < mag) (e : ℕ)
    (he : e ≤ 2*ratBits mag) (hepos : 0 < e) :
    ∀ r ∈ powerSearchOperands fuel (normalizedMagnitude mag) ((2 : ℚ)^e),
      ∃ f ≤ 2*ratBits mag, r = (2 : ℚ)^f := by
  let z := normalizedMagnitude mag
  induction fuel generalizing e with
  | zero =>
    intro r h
    simp only [powerSearchOperands, List.mem_singleton] at h
    exact ⟨e,he,h⟩
  | succ n ih =>
    intro r hr
    change r ∈ powerSearchOperands (n+1) z (2^e) at hr
    by_cases h : z < (2 : ℚ)^e
    · simp only [powerSearchOperands, ite_eq_left h, List.mem_singleton] at hr
      exact ⟨e,he,hr⟩
    · have he' : e ≤ ratBits mag := exponent_le_ratBits hm (le_of_not_gt h)
      have hp : (2 : ℚ)^e*(2^e) = 2^(2*e) := by rw [two_mul, pow_add]
      simp only [powerSearchOperands, ite_eq_right h, hp, List.mem_cons, List.mem_append] at hr
      rcases hr with hroot | hchild | htry
      · exact ⟨e,he,hroot⟩
      · exact ih (2*e) (by omega) (by omega) r hchild
      · let base := (2 : ℚ)^(2*e)
        have hbase : 1 < base := one_lt_pow₀ (by norm_num) (by omega)
        have hs := (powerSearch_spec n z base (one_le_normalizedMagnitude hm) hbase).2
        change r ∈ (match (powerSearch n z base).answer with
                    | none => [] | some (_, q) => [q * (2 : ℚ)^e]) at htry
        cases hh : (powerSearch n z base).answer with
        | none => simp [hh] at htry
        | some pair =>
          rcases pair with ⟨j,q⟩
          rw [hh] at hs
          obtain ⟨hq,hqz,_,_⟩ := hs
          have hq' : q = (2 : ℚ)^(2*e*j) := by
            rw [hq, pow_mul]
          have hf : 2*e*j ≤ ratBits mag := exponent_le_ratBits hm (hq' ▸ hqz)
          simp only [hh, List.mem_singleton] at htry
          exact ⟨2*e*j+e, by omega, by rw [htry,hq',pow_add]⟩

/-- Every rational power or trial product compared by the concrete range search is a power
of two with exponent at most twice the original input's binary length. -/
theorem powerSearchOperands_spec (fuel : ℕ) {mag : ℚ} (hm : 0 < mag) (r : ℚ)
    (hr : r ∈ powerSearchOperands fuel (normalizedMagnitude mag) 2) :
    ∃ e ≤ 2*ratBits mag, r = (2 : ℚ)^e := by
  have hb : 1 ≤ 2 * ratBits mag := by unfold ratBits; omega
  exact operands_exponents fuel mag hm 1 hb (by decide) r (by simpa using hr)

/-- The upper cutoff can be exponentially larger than the input bit length, but it never
appears as a scalar exponent on that input unless justified by an actual minor magnitude. -/
theorem powerSearchOperands_ratBits (fuel : ℕ) {mag : ℚ} (hm : 0 < mag) :
    ∀ r ∈ powerSearchOperands fuel (normalizedMagnitude mag) 2, ratBits r ≤ 3 + 8*ratBits mag := by
  intro r hr
  obtain ⟨e,he,rfl⟩ := powerSearchOperands_spec fuel hm r hr
  have h := ratBits_natPow_le (2 : ℚ) e
  have h₂ : ratBits (2 : ℚ) = 4 := rfl
  rw [h₂] at h
  omega

end Compression
end LinearProgramming
end Optimization
end OAI

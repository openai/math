import OAI.Optimization.LinearProgramming.Compression.ProxyProgram
import OAI.Optimization.LinearProgramming.FieldTransfer.Proxy

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open OAI.Optimization.LinearProgramming.RAM OAI.Optimization.LinearProgramming.FieldTransfer

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The optional signed dyadic numerator denoted by the same field algorithm, without
using an analytic logarithm or coercing input scalars to the rationals. -/
def fieldProxyNumerator (fuel k : ℕ) (mag : K) : Option ℤ :=
  let z := normalizedRangeInput mag
  match rangeAnswer fuel z 2 with
  | none => none
  | some (e,q) =>
    let n := 2 ^ (k+2) * e + (mantissaGridNumerator (z/q) k).1
    some (if mag < 1 then -(n:ℤ) else (n:ℤ))

theorem fieldProxyNumerator_rat (fuel k : ℕ) (q : ℚ) :
    fieldProxyNumerator fuel k q = logProxyNumerator fuel k q := by
  have hn : normalizedRangeInput q = normalizedMagnitude q := by
    by_cases h : q < 1 <;> simp [normalizedRangeInput,normalizedMagnitude,h]
  simp only [fieldProxyNumerator, hn,rangeAnswer_rat_eq,logProxyNumerator]
  cases (powerSearch fuel (normalizedMagnitude q) 2).answer with
  | none => rfl
  | some a => rcases a with ⟨e,v⟩; by_cases h : q < 1 <;> simp [h]

theorem fieldProxyNumerator_real (fuel k : ℕ) (q : ℝ) :
    fieldProxyNumerator fuel k q = RealProxy.numerator fuel k q := by
  have hn : normalizedRangeInput q = RealProxy.normalizedMagnitude q := by
    by_cases h : q < 1 <;> simp [normalizedRangeInput,RealProxy.normalizedMagnitude,h]
  simp only [fieldProxyNumerator, hn,rangeAnswer_field_eq,RealProxy.numerator]
  cases (RealProxy.powerSearch fuel (RealProxy.normalizedMagnitude q) 2).answer with
  | none => rfl
  | some a => rcases a with ⟨e,v⟩; by_cases h : q < 1 <;> simp [h]

theorem logProxyProgram_field_exec_from (fuel k : ℕ) {mag : K} (hm : 0 < mag) (input : State K)
    (pc0 : input.pc = 0) (live : input.output = none) (input0 : input.data 0 = mag)
    (ifuel : input.index 0 = fuel) (ik : input.index 1 = k) :
    ∃ ell ≤ 16*fuel+27*k+210, ∃ t : Fin (ell+1) → State K,
      Trace logProxyProgram input ell t ∧
      (match fieldProxyNumerator fuel k mag with
       | none => (t (Fin.last _)).output = some 1
       | some u => (t (Fin.last _)).output = some 0 ∧
           (t (Fin.last _)).data 0 = (u : K)/2^(k+2)) := by
  obtain ⟨ell,hell,t,ht,hout⟩ := logProxyProgram_trace_from fuel k hm input pc0 live input0 ifuel ik
  refine ⟨ell,hell,t,ht,?_⟩
  by_cases hs : rangeAnswer fuel (normalizedRangeInput mag) 2 = none
  · have hdata : fieldProxyNumerator fuel k mag = none := by simp only [fieldProxyNumerator,hs]
    rw [hdata]
    simpa only [hs] using hout
  · obtain ⟨⟨e,q⟩,he⟩ := Option.ne_none_iff_exists'.mp hs
    rw [he] at hout
    obtain ⟨ho,hv,_⟩ := hout
    simp only [fieldProxyNumerator,he]
    refine ⟨ho,?_⟩
    rw [hv]
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using signed_grid_value (K := K) (2^(k+2)) e
      (mantissaGridNumerator (normalizedRangeInput mag/q) k).1 (by positivity) (mag < 1)

/-- The complete output word has a dimension-bounded length even for non-Archimedean
input fields. Only the integer produced by field comparisons occurs in the estimate. -/
theorem fieldProxy_word_length (fuel k : ℕ) {mag : K} (hm : 0 < mag) {u : ℤ}
    (hu : fieldProxyNumerator fuel k mag = some u) : u.natAbs < 2^(fuel+k+2) := by
  let z := normalizedRangeInput mag
  have hn : normalizedRangeInput mag = RealProxy.normalizedMagnitude mag := by
    by_cases h : mag < 1 <;> simp [normalizedRangeInput,RealProxy.normalizedMagnitude,h]
  have hzone : 1 ≤ z := by change 1 ≤ normalizedRangeInput mag; rw [hn]; exact RealProxy.one_le_normalizedMagnitude hm
  have hspec := (RealProxy.powerSearch_spec fuel z (2:K) hzone (by norm_num)).2
  rw [← rangeAnswer_field_eq] at hspec
  cases hr : rangeAnswer fuel z 2 with
  | none =>
    have hnone : fieldProxyNumerator fuel k mag = none := by
      simp only [fieldProxyNumerator,← show z=normalizedRangeInput mag from rfl,hr]
    rw [hnone] at hu
    contradiction
  | some pair =>
    rcases pair with ⟨e,q⟩
    rw [hr] at hspec
    obtain ⟨_,_,_,he⟩ := hspec
    let digit := (mantissaGridNumerator (z/q) k).1
    have hd : digit < 2^(k+2) := (mantissaGrid_cost (z/q) k).2
    have hlim : 2^(k+2)*e+digit < 2^(fuel+k+2) := calc
      _ < 2^(k+2)*(e+1) := by rw [Nat.mul_succ]; omega
      _ ≤ 2^(k+2)*2^fuel := Nat.mul_le_mul_left _ he
      _ = _ := by rw [←pow_add]; congr 1; omega
    unfold fieldProxyNumerator at hu
    simp only [← show z=normalizedRangeInput mag from rfl,hr,Option.some.injEq] at hu
    subst u
    by_cases h : mag < 1
    · simpa only [ite_eq_left h,Int.natAbs_neg,Int.natAbs_natCast] using hlim
    · simpa only [ite_eq_right h,Int.natAbs_natCast] using hlim

theorem scaledFieldProxy_for_bits (fuel k : ℕ) (u : ℤ) :
    |(u : K) / 2^(k+2)| / (2 : K)^fuel = (u.natAbs : K) / 2^(fuel+k+2) := by
  have hh : (u.natAbs : K) = |(u : K)| := calc
    _ = ((u.natAbs : ℤ) : K) := (Int.cast_natCast _).symm
    _ = _ := by rw [Int.natCast_natAbs,Int.cast_abs]
  rw [hh,abs_div,abs_of_pos (by positivity : (0 : K) < 2^(k+2)),div_div]
  congr 1
  rw [←pow_add]
  congr 1
  omega

end Compression
end LinearProgramming
end Optimization
end OAI

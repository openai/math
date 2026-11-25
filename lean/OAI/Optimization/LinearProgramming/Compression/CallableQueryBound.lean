import OAI.Optimization.LinearProgramming.Compression.CallableDirectProxy
import OAI.Optimization.LinearProgramming.Compression.PreparedWindow

/-! A uniform allocation and time polynomial for repeated native proxy comparisons. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open OAI.Optimization.LinearProgramming.RAM RAM.Callable
open scoped BigOperators

def fixedProxyAddressBudget : ℕ := addressBudget literalPowerCompareProgram + addressBudget smallAffineProgram

def reentrantQueryCap (n fuel : ℕ) : ℕ :=
  max fixedProxyAddressBudget ((preparedProxyRawSpan n fuel)^2) + proxyQuerySteps n fuel

/-- A single allocation and reset window works for every admissible query at this
number of terms and cutoff, including all branches and every possible rational base. -/
theorem directProxyWindow_le_reentrantQueryCap {n : ℕ} (fuel prec B : ℕ) {A : ℤ}
    (c : ℤ) (a : Fin n → ℤ) (mag : Fin n → ℚ) (hm : ∀ i, 0<mag i)
    (hbits : ∀ i, ratBits (mag i) ≤ B) (hform : |c|+∑ i,|a i|≤A)
    (hcut : (2:ℤ)^prec*A≤2^fuel) :
    directProxyWindow (preparedProxyQuery fuel prec c a mag) + proxyQuerySteps n fuel ≤ reentrantQueryCap n fuel := by
  have l := preparedProxyQuery_raw_nativeWindow literalPowerCompareProgram fuel prec B c a mag hm hbits hform hcut
  have r := preparedProxyQuery_raw_nativeWindow smallAffineProgram fuel prec B c a mag hm hbits hform hcut
  apply Nat.add_le_add_right
  exact max_le (l.trans (max_le_max_right _ (Nat.le_add_right _ _)))
    (r.trans (max_le_max_right _ (Nat.le_add_left _ _)))

/-- The fixed code and finite reset loop give a fourth-degree bound in the term count
plus cutoff bit length. This includes the return table, input stages, and runtime tests. -/
theorem reentrantQueryTime_le_poly (n fuel : ℕ) :
    19*(reentrantQueryCap n fuel+1)+225+(2*proxyQuerySteps n fuel+4) ≤
      polyBound (20*fixedProxyAddressBudget+250000) 4 (n+fuel) := by
  let s := n+fuel+1
  have h1 : 1≤s := by dsimp [s]; omega
  have hn : n≤s := by dsimp [s]; omega
  have hf : fuel≤s := by dsimp [s]; omega
  have h2 : s≤s^2 := Nat.le_self_pow (by decide) s
  have h24 : s^2≤s^4 := calc
    s^2 ≤ (s^2)^2 := Nat.le_self_pow (by decide) _
    _ = s^4 := by ring
  have hprod : n*fuel≤s^2 := by simpa only [pow_two] using Nat.mul_le_mul hn hf
  have ht : preparedTokenBudget n fuel≤24*s^2 := by unfold preparedTokenBudget; nlinarith
  have hr : preparedProxyRawSpan n fuel≤90*s^2 := by unfold preparedProxyRawSpan; nlinarith
  have ht' : proxyQuerySteps n fuel≤730*s^2 := by
    unfold proxyQuerySteps
    apply max_le
    · nlinarith
    · change 30*preparedTokenBudget n fuel+9≤_
      nlinarith
  have hr2 : (preparedProxyRawSpan n fuel)^2 ≤ 8100*s^4 := by
    calc (preparedProxyRawSpan n fuel)^2 ≤ (90*s^2)^2 := Nat.pow_le_pow_left hr 2
         _ = _ := by ring
  have hmax : max fixedProxyAddressBudget ((preparedProxyRawSpan n fuel)^2) ≤ fixedProxyAddressBudget+8100*s^4 :=
    max_le (Nat.le_add_right _ _) (hr2.trans (Nat.le_add_left _ _))
  have hM : fixedProxyAddressBudget≤fixedProxyAddressBudget*s^4 := by
    have h1' : 1≤s^4 := Nat.one_le_pow 4 s h1
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left fixedProxyAddressBudget h1'
  change 19*((max fixedProxyAddressBudget ((preparedProxyRawSpan n fuel)^2)+proxyQuerySteps n fuel)+1)+
    225+(2*proxyQuerySteps n fuel+4) ≤ (20*fixedProxyAddressBudget+250000)*s^4
  nlinarith

end Compression
end LinearProgramming
end Optimization
end OAI

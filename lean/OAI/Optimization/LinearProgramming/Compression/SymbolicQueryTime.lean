import OAI.Optimization.LinearProgramming.Compression.SymbolicAreas
import OAI.Optimization.LinearProgramming.Compression.CallableQueryBound

/-! Running-time and scalar bit budgets for staging and executing the mixed query. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM RAM.Callable

def symbolicQueryCap (n fuel : ℕ) := max (reentrantQueryCap n fuel) (11*(n+1)+42)

def symbolicQueryBits (n fuel prec B : ℕ) :=
  max (proxyQueryBits n fuel prec B) (2*(2*fuel+3)+5)

def symbolicQuerySteps (n fuel C : ℕ) :=
  4*(21*n+57) + ((19*(C+1)+225+(2*(9*(n+1)+3)+3)) +
    (4*(17*n+18) + (4*symbolicEncodeSteps (n+1) (2*fuel+3) +
      (19*(C+1)+225+(2*proxyQuerySteps n fuel+4)))))

theorem symbolicQueryTime_le_poly (n fuel : ℕ) :
    symbolicQuerySteps n fuel (symbolicQueryCap n fuel) ≤
      polyBound (40*fixedProxyAddressBudget+610000) 4 (n+fuel) := by
  let s := n+fuel+1
  have hs : 1 ≤ s := by dsimp [s]; omega
  have hn : n+1 ≤ s := by dsimp [s]; omega
  have hf : fuel ≤ s := by dsimp [s]; omega
  have hs2 : s ≤ s^2 := Nat.le_self_pow (by decide) s
  have hs23 : s^2 ≤ s^3 := Nat.pow_le_pow_right hs (by decide)
  have hs34 : s^3 ≤ s^4 := Nat.pow_le_pow_right hs (by decide)
  have w : 2*fuel+3 ≤ 5*s := by omega
  have inner : 16*(2*fuel+3)+32 ≤ 112*s := by omega
  have prod := Nat.mul_le_mul w inner
  have coef : (2*fuel+3)*(16*(2*fuel+3)+32)+37 ≤ 597*s^2 := by nlinarith
  have cubic := Nat.mul_le_mul coef hn
  have tape := Nat.mul_le_mul hn (show (2*fuel+3)+2 ≤ 7*s by omega)
  have pack : symbolicEncodeSteps (n+1) (2*fuel+3) ≤ 800*s^3 := by
    unfold symbolicEncodeSteps
    nlinarith
  have cap : symbolicQueryCap n fuel ≤ reentrantQueryCap n fuel + (11*(n+1)+42) := by
    exact max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
  have old := reentrantQueryTime_le_poly n fuel
  change _ ≤ (20*fixedProxyAddressBudget+250000)*s^4 at old
  change symbolicQuerySteps n fuel (symbolicQueryCap n fuel) ≤ (40*fixedProxyAddressBudget+610000)*s^4
  unfold symbolicQuerySteps
  nlinarith

end Compression
end LinearProgramming
end Optimization
end OAI

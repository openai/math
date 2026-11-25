import Mathlib.Tactic.Linarith
import OAI.Optimization.LinearProgramming.Compression.SignWireCost

/-! Explicit polynomial majorants for the complete numerical word comparator
and the linked adaptive bisection, including all register and packet costs. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace SignWire
open RAM

theorem cachedProxySteps_le_symbolic (n fuel C : ℕ) :
    cachedProxySignSteps n fuel C ≤ symbolicQuerySteps n fuel C+2 := by
  unfold cachedProxySignSteps allSmallCacheCallSteps symbolicQuerySteps
  exact max_le (by omega) (by omega)

/-- The entire word callback has a fourth-degree instruction bound in the
number of generators and the chosen cutoff, independent of magnitude bits. -/
theorem wordComparatorTime_le_poly (n fuel : ℕ) :
    wordComparatorTime n fuel (symbolicQueryCap n fuel) ≤
      polyBound (80*fixedProxyAddressBudget+1220300) 4 (n+fuel) := by
  let s := n+fuel+1
  have h1 : 1 ≤ s := by dsimp [s];omega
  have hn : n+1 ≤ s := by dsimp [s];omega
  have hf : 2*(fuel+1)+2 ≤ 4*s := by dsimp [s];omega
  have product := Nat.mul_le_mul hn hf
  have h14 : s ≤ s^4 := Nat.le_self_pow (by decide) s
  have h24 : s^2 ≤ s^4 := Nat.pow_le_pow_right h1 (by decide)
  have hsym := symbolicQueryTime_le_poly n fuel
  change symbolicQuerySteps n fuel (symbolicQueryCap n fuel) ≤ (40*fixedProxyAddressBudget+610000)*s^4 at hsym
  have hmerge := cachedProxySteps_le_symbolic n fuel (symbolicQueryCap n fuel)
  unfold wordComparatorTime numericalTagCost isolatedCachedCost
  change _ ≤ (80*fixedProxyAddressBudget+1220300)*s^4
  nlinarith

/-- All rational registers, including the proxy-product intermediates, have
cubic bit length in the dimension, cutoff, grid precision and the bit length
of the input magnitudes. -/
theorem wordComparatorBits_le_poly (n fuel prec B : ℕ) :
    wordComparatorBits n fuel prec B ≤ polyBound 100 3 (n+fuel+prec+B) := by
  let s := n+fuel+prec+B+1
  have h1 : 1 ≤ s := by dsimp [s];omega
  have hn : n ≤ s := by dsimp [s];omega
  have hf : fuel ≤ s := by dsimp [s];omega
  have hb : B ≤ s := by dsimp [s];omega
  have h13 : s ≤ s^3 := Nat.le_self_pow (by decide) s
  have h23 : s^2 ≤ s^3 := Nat.pow_le_pow_right h1 (by decide)
  have lin := Nat.mul_le_mul (show 2*(n+1)+3 ≤ 7*s by omega)
    (show prec+2+fuel+1 ≤ 5*s by dsimp [s];omega)
  have square := Nat.mul_le_mul hb hb
  have cross := Nat.mul_le_mul (show 4*B+1 ≤ 5*s by omega) hb
  have inner : 3+(4*B+1)*B ≤ 8*s^2 := by nlinarith [Nat.le_self_pow (by decide : (2 : ℕ) ≠ 0) s]
  have cubic := Nat.mul_le_mul hn inner
  unfold wordComparatorBits symbolicQueryBits proxyQueryBits polyBound
  change max (max (max _ _) _) _ ≤ 100*s^3
  refine max_le (max_le (max_le ?_ ?_) ?_) ?_ <;> nlinarith

/-- If a bisection uses k adaptive queries, every comparison, array write
and controller save/restore still fits in a fifth-degree operation budget. -/
theorem cachedSearchTime_le_poly (n fuel k : ℕ) :
    k*(4*(12*(n+1)+5)+(32+(cachedProxySignSteps n fuel (symbolicQueryCap n fuel)+32))+18)+13 ≤
      polyBound (40*fixedProxyAddressBudget+611000) 5 (n+fuel+k) := by
  let s := n+fuel+k+1
  have h1 : 1 ≤ s := by dsimp [s];omega
  have hn : n+1 ≤ s := by dsimp [s];omega
  have hk : k ≤ s := by dsimp [s];omega
  have h14 : s ≤ s^4 := Nat.le_self_pow (by decide) s
  have q := symbolicQueryTime_le_poly n fuel
  have hp : (n+fuel+1)^4 ≤ s^4 := Nat.pow_le_pow_left (by dsimp [s];omega) 4
  have q' : symbolicQuerySteps n fuel (symbolicQueryCap n fuel) ≤ (40*fixedProxyAddressBudget+610000)*s^4 :=
    q.trans (Nat.mul_le_mul_left _ hp)
  have merge := cachedProxySteps_le_symbolic n fuel (symbolicQueryCap n fuel)
  have cost : 4*(12*(n+1)+5)+(32+(cachedProxySignSteps n fuel (symbolicQueryCap n fuel)+32))+18 ≤
      (40*fixedProxyAddressBudget+610200)*s^4 := by nlinarith
  have total := Nat.mul_le_mul hk cost
  unfold polyBound
  change _ ≤ (40*fixedProxyAddressBudget+611000)*s^5
  rw [pow_succ s 4]
  nlinarith

end SignWire
end Compression
end LinearProgramming
end Optimization
end OAI

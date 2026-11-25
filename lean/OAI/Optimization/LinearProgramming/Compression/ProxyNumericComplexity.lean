import OAI.Optimization.LinearProgramming.Compression.ProxyNumericCache
import OAI.Optimization.LinearProgramming.Compression.MinorProxyCacheComplexity
import OAI.Optimization.LinearProgramming.Compression.AdaptiveRequests

/-! The normal numerical cache has a dimension-only polynomial clock and a
separate polynomial operand-length bound for its entire native trace. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM Polynomial MinorProxyCache

private noncomputable def initPolynomial : Polynomial ℕ :=
  parameterResourcePolynomialFromCoefficients manuscriptProxyFuelCoefficients manuscriptProxyFuelPolynomial

private noncomputable def cacheInputPolynomial : Polynomial ℕ :=
  let w := (X+1)^6
  let f := manuscriptProxyFuelPolynomial
  let k := parameterGridExponent
  (w+1)+f+k+(w+8)+((8+k+1)+f+1)

noncomputable def numericCacheClockPolynomial : Polynomial ℕ :=
  let w := (X+1)^6
  let f := manuscriptProxyFuelPolynomial
  let k := parameterGridExponent
  (7*w+15) + (4+(initPolynomial+(20+((4*f+4)+(4*k+4))))) +
    cacheClockPolynomial.comp cacheInputPolynomial

noncomputable def numericCacheBitsPolynomial : Polynomial ℕ :=
  let f := manuscriptProxyFuelPolynomial
  let k := parameterGridExponent
  X+initPolynomial+f+k+6 + C proxySizeCoefficient*(X+3+f+k+1)^3

private theorem eval_monotone (p : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) : p.eval a ≤ p.eval b := by
  rw [eval_eq_sum,eval_eq_sum]
  unfold Polynomial.sum
  apply Finset.sum_le_sum
  intro i _
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h i)

private theorem init_resources (N : ℕ) :
    parameterStepsFromCoefficients manuscriptProxyFuelCoefficients N ≤ initPolynomial.eval N ∧
    parameterBits manuscriptProxyFuelPolynomial N ≤ initPolynomial.eval N := by
  have hc (n : ℕ) : parameterCoefficientValue manuscriptProxyFuelCoefficients n =
      manuscriptProxyFuelPolynomial.eval n :=
    (manuscriptProxyFuelCoefficients_value n).trans (manuscriptProxyFuelPolynomial_eval n).symm
  have h := parameterListResourcePolynomial_eval manuscriptProxyFuelCoefficients manuscriptProxyFuelPolynomial hc N
  change initPolynomial.eval N = _ at h
  omega

theorem numericProxyCacheSteps_le (N g : ℕ) (hg : g ≤ paperWidth N) :
    numericProxyCacheSteps N g + 1 ≤ numericCacheClockPolynomial.eval N := by
  let f := manuscriptProxyFuel N
  let k := numericCachePrecision N
  let r := numericCacheAddressEnd N
  let b := initPolynomial.eval N
  have hp := (init_resources N).1
  have hw : g ≤ (N+1)^6 := hg
  have harg : (g+1)+f+k+(g+8)+r ≤ cacheInputPolynomial.eval N := by
    simp only [cacheInputPolynomial,eval_add,eval_pow,eval_X,eval_one,eval_ofNat,
      manuscriptProxyFuelPolynomial_eval,parameterGridExponent_eval]
    change (g+1)+f+k+(g+8)+((8+k+1)+f+1) ≤
      ((N+1)^6+1)+f+k+((N+1)^6+8)+((8+k+1)+f+1)
    omega
  have hc := (fromPositiveCost_le_polynomial (g+1) f k (g+8) r).trans
    (eval_monotone cacheClockPolynomial harg)
  simp only [numericCacheClockPolynomial,eval_add,eval_mul,eval_pow,eval_X,eval_one,eval_ofNat,
    eval_comp,manuscriptProxyFuelPolynomial_eval,parameterGridExponent_eval]
  unfold numericProxyCacheSteps normalProxyHeaderSteps
  rw [manuscriptProxyFuelCoefficients_value]
  change (7*g+15+(4+(parameterStepsFromCoefficients manuscriptProxyFuelCoefficients N+
      (20+((4*f+4)+(4*k+4)))))) + fromPositiveCost (g+1) f k (g+8) r + 1 ≤
    7*(N+1)^6+15 + (4+(b+(20+((4*f+4)+(4*k+4))))) +
      cacheClockPolynomial.eval (cacheInputPolynomial.eval N)
  omega

theorem numericProxyCacheBits_le (N B : ℕ) :
    numericProxyCacheBits N B ≤ numericCacheBitsPolynomial.eval (N+B) := by
  have hn : N ≤ N+B := by omega
  have hq := (init_resources N).2.trans (eval_monotone initPolynomial hn)
  have hf : manuscriptProxyFuel N ≤ manuscriptProxyFuelPolynomial.eval (N+B) :=
    (manuscriptProxyFuelPolynomial_eval N) ▸ eval_monotone manuscriptProxyFuelPolynomial hn
  have hk : numericCachePrecision N ≤ parameterGridExponent.eval (N+B) := calc
    numericCachePrecision N = parameterGridExponent.eval N := (parameterGridExponent_eval N).symm
    _ ≤ parameterGridExponent.eval (N+B) := eval_monotone parameterGridExponent hn
  have hmax : max B (parameterBits manuscriptProxyFuelPolynomial N) ≤
      (N+B)+initPolynomial.eval (N+B) := max_le (by omega) (by omega)
  have hbase : B+3+manuscriptProxyFuel N+numericCachePrecision N+1 ≤
      (N+B)+3+manuscriptProxyFuelPolynomial.eval (N+B)+parameterGridExponent.eval (N+B)+1 := by omega
  have hc := Nat.mul_le_mul_left proxySizeCoefficient (Nat.pow_le_pow_left hbase 3)
  simp only [numericCacheBitsPolynomial,eval_add,eval_mul,eval_pow,eval_X,eval_one,eval_ofNat,eval_C]
  unfold numericProxyCacheBits cacheBits polyBound
  exact Nat.add_le_add (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hmax hf) hk) 6) hc

/-- Fixed bounds for the entire initialized batch as called from an online request. -/
theorem numericProxyCache_stronglyPolynomial :
    ∃ c₁ d₁ c₂ d₂ : ℕ, ∀ (N g rank B : ℕ) (member : Bool) (mag : Fin (g+1) → ℚ),
      g ≤ paperWidth N → (∀ i, 0 < mag i) → (∀ i, ratBits (mag i) ≤ B) →
      ∃ k ≤ polyBound c₁ d₁ N, ∃ tr : Fin (k+1) → State ℚ,
        Trace (numericProxyCache.program 0) (start [N,g,member.toNat,rank] (List.ofFn mag)) k tr ∧
        (tr (Fin.last k)).output = some 0 ∧
        StableCache (tr (Fin.last k)).memory (numericProxyCacheBuffers N g) (g+1) (manuscriptProxyFuel N)
          (numericCachePrecision N) (tapeMagnitude mag) ∧
        (tr (Fin.last k)).index 90 = N ∧ (tr (Fin.last k)).index 91 = g ∧
        (tr (Fin.last k)).index 92 = member.toNat ∧ (tr (Fin.last k)).index 93 = rank ∧
        ProxyDriverMetadata N g member.toNat rank (tr (Fin.last k)).memory ∧
        ∀ i, scalarBound (polyBound c₂ d₂ (N+B)) (tr i) := by
  refine ⟨numericCacheClockPolynomial.eval 1,numericCacheClockPolynomial.natDegree,
    numericCacheBitsPolynomial.eval 1,numericCacheBitsPolynomial.natDegree,?_⟩
  intro N g rank B member mag hg hp hm
  obtain ⟨k,hk,tr,ht,tag,cache,h90,h91,h92,h93,stable,hbits⟩ :=
    numericProxyCache_trace N g rank B member mag hp hm
  exact ⟨k,hk.trans ((numericProxyCacheSteps_le N g hg).trans (polynomial_eval_le_polyBound _ _)),
    tr,ht,tag,cache,h90,h91,h92,h93,stable,fun i j => (hbits i j).trans
      ((numericProxyCacheBits_le N B).trans (polynomial_eval_le_polyBound _ _))⟩

end Compression
end LinearProgramming
end Optimization
end OAI

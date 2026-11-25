import OAI.Optimization.LinearProgramming.Compression.MinorProxyCacheStart
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! Uniform polynomial envelopes for the prepared cache entry and its ordinary finite tape. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace MinorProxyCache
open RAM

/-- The full entry, including its final halt, takes at most this fixed quadratic. -/
theorem fromPositiveCost_le_quadratic (n fuel prec src addressEnd : ℕ) :
    fromPositiveCost n fuel prec src addressEnd+1 ≤ polyBound 1000 2 (n+fuel+prec+src+addressEnd) := by
  let S := n+fuel+prec+src+addressEnd
  have hn : n≤S := by dsimp [S]; omega
  have hf : fuel≤S := by dsimp [S]; omega
  have hp : prec≤S := by dsimp [S]; omega
  have hh : headerCost n fuel prec src addressEnd ≤ 634+28*S := by dsimp [headerCost,S]; omega
  rw [fromPositiveCost,allocationCost_eq,cacheCost,visitCost,cap]
  have mul := Nat.mul_le_mul hn (show 4*(fuel+prec+20)+16*fuel+27*prec+228+2≤51*S+310 by omega)
  have cap' : 634+28*S+7*S+4*S+13+(S*(51*S+310)+9)+1≤1000*(S+1)^2 := by ring_nf; omega
  change _ ≤ 1000*(S+1)^2
  omega

/-- The same numeric clock packaged for substitution into an enclosing RAM program. -/
noncomputable def cacheClockPolynomial : Polynomial ℕ := 1000*(Polynomial.X+1)^2

theorem cacheClockPolynomial_eval (s : ℕ) : cacheClockPolynomial.eval s=polyBound 1000 2 s := by
  simp [cacheClockPolynomial,polyBound]

theorem fromPositiveCost_le_polynomial (n fuel prec src addressEnd : ℕ) :
    fromPositiveCost n fuel prec src addressEnd+1 ≤ cacheClockPolynomial.eval (n+fuel+prec+src+addressEnd) := by
  rw [cacheClockPolynomial_eval]
  exact fromPositiveCost_le_quadratic n fuel prec src addressEnd

theorem normal_cacheBits_le (B fuel prec : ℕ) :
    cacheBits (B+3) B fuel prec ≤ polyBound (9+64*proxySizeCoefficient) 3 (B+fuel+prec) := by
  let x := B+fuel+prec+1
  have hx : 1≤x := by dsimp [x]; omega
  have heq : B+3+fuel+prec+1=x+3 := by dsimp [x]; omega
  have hpow : (x+3)^3≤(4*x)^3 := Nat.pow_le_pow_left (by omega) _
  have hlin : B+3+fuel+prec+6≤9*x^3 := by
    have h : x≤x^3 := by
      calc x = x^1 := (pow_one x).symm
           _ ≤ _ := Nat.pow_le_pow_right hx (by decide)
    dsimp [x] at h ⊢; omega
  unfold cacheBits polyBound
  rw [heq]
  change B+3+fuel+prec+6+proxySizeCoefficient*(x+3)^3 ≤ (9+64*proxySizeCoefficient)*x^3
  calc
    _ ≤ 9*x^3+proxySizeCoefficient*(4*x)^3 := Nat.add_le_add hlin (Nat.mul_le_mul_left _ hpow)
    _ = _ := by ring

/-- The ordinary RAM entry has a dimension/precision operation clock and a separate
cubic encoding bound for every rational in the same execution. -/
theorem normal_entry {n : ℕ} (B fuel prec : ℕ) (mag : Fin n→ℚ) (positive : ∀i,0<mag i)
    (words : ∀i,ratBits (mag i)≤B) :
    let m := start [n,fuel,prec,0,0] (List.ofFn mag)
    ∃ k≤polyBound 1000 2 (n+fuel+prec),
      ∃ tr : Fin (k+1)→State ℚ, Trace (fromPositive.program 0) m k tr ∧
        (tr (Fin.last k)).output=some 0 ∧
        StableCache (tr (Fin.last k)).memory (buffers n fuel prec 0 0) n fuel prec (tapeMagnitude mag) ∧
        ∀j,scalarBound (polyBound (9+64*proxySizeCoefficient) 3 (B+fuel+prec)) (tr j) := by
  obtain ⟨k,hk,tr,run,tag,out,safe⟩ := fromPositive_rational B fuel prec mag positive words
  have hc := fromPositiveCost_le_quadratic n fuel prec 0 0
  simp only [Nat.add_zero] at hc
  exact ⟨k,hk.trans hc,tr,run,tag,out,
    fun j a => (safe j a).trans (normal_cacheBits_le B fuel prec)⟩

end MinorProxyCache
end Compression
end LinearProgramming
end Optimization
end OAI

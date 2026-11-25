import OAI.Optimization.LinearProgramming.Compression.SmallProxy
import OAI.Optimization.LinearProgramming.Compression.SmallAffineMachine

/-! Native execution of the all-small case. The two integer arrays contain ordinary
constructed bits interpreted as scalars; their first pair is the denominator and
the affine constant. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open OAI.Optimization.LinearProgramming.RAM
open scoped BigOperators

theorem computedSmallProxyRAM_correct {n : ℕ} (fuel prec : ℕ) {A : ℤ} (c : ℤ)
    (a : Fin n → ℤ) (mag : Fin n → ℚ) (hm : ∀ i, 0 < mag i)
    (hform : |c| + ∑ i, |a i| ≤ A) (hcut : (2 : ℤ)^prec * A ≤ 2^fuel)
    (hsmall : ∀ i, logProxyNumerator fuel prec (mag i) ≠ none) :
    let D := (2 : ℕ)^(prec+2)
    let grid i := (logProxyNumerator fuel prec (mag i)).getD 0
    let left := smallProxyLeft D a
    let right := smallProxyRight c grid
    let form := (c : ℝ) + ∑ i, (a i : ℝ) *
      logProxyValue prec (mag i) (logProxyNumerator fuel prec (mag i))
    ∃ k ≤ 9*(n+1)+6, ∃ tr : Fin (k+1) → State ℚ,
      Trace smallAffineProgram (start [n+1] (0 :: 0 :: 0 :: affineInputPairs left right)) k tr ∧
      (tr (Fin.last k)).output = some (if form < 0 then 0 else if 0 < form then 2 else 1) ∧
      (tr (Fin.last k)).data 0 = (clearedProxyOffset ∅ D c a grid : ℚ) ∧
      ∀ i, scalarBound (3 + 2*((n+2) + (2*(n+1)+3)*(prec+2+fuel+1))) (tr i) := by
  let D := (2 : ℕ)^(prec+2)
  let grid i := (logProxyNumerator fuel prec (mag i)).getD 0
  let H := (2 : ℕ)^(prec+2+fuel)
  obtain ⟨hl,hr⟩ := computedProxy_input_heights fuel prec c a mag hm hform hcut
  have h₀ : (0 : ℚ).num.natAbs ≤ H ∧ (0 : ℚ).den ≤ H := by
    have hH : 1 ≤ H := one_le_pow₀ (by decide : (1 : ℕ) ≤ 2)
    exact ⟨by simp, by simpa using hH⟩
  obtain ⟨k,hk,tr,ht,ho,hv,hs⟩ :=
    smallAffineProgram_trace (smallProxyLeft D a) (smallProxyRight c grid) 0 hl hr h₀
  simp only [zero_add] at ho hv
  have hD : 0 < D := by dsimp [D]; positivity
  have hc := smallProxyDot_sign D hD c a grid mag
  change smallAffineTag (dotProduct (smallProxyLeft D a) (smallProxyRight c grid)) = _ at hc
  have hlarge : (Finset.univ.filter fun i => logProxyNumerator fuel prec (mag i) = none) = ∅ := by
    ext i
    simp [hsmall i]
  have hreal := logProxyAffine_eq fuel prec c a mag
  change proxyAffine (Finset.univ.filter fun i => logProxyNumerator fuel prec (mag i) = none) D c a grid mag = _ at hreal
  rw [hlarge] at hreal
  rw [hc,hreal] at ho
  rw [smallProxyDot_value] at hv
  have hb : affineEvalBits (n+1) H = 3 + 2*((n+2) + (2*(n+1)+3)*(prec+2+fuel+1)) := by
    simp [affineEvalBits,H,Nat.log2_two_pow]
  exact ⟨k,hk,tr,ht,ho,hv,fun i => hb ▸ hs i⟩

end Compression
end LinearProgramming
end Optimization
end OAI

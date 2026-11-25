import OAI.Optimization.LinearProgramming.Compression.ProxyFuelQueries
import OAI.Optimization.LinearProgramming.Compression.RequestNative
import OAI.Optimization.LinearProgramming.Compression.ProxyCost

/-! Bounds on the actual comparisons issued by native LLL-based rounding and residual search. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open OAI.Optimization.LinearProgramming.Lattice OAI.Optimization.LinearProgramming.RAM
open scoped BigOperators

/-- The sign requests made by the LLL selector, on a list of magnitudes of the current size. -/
def nativeRoundingHistory {d : ℕ} (N M : ℕ) (mag : Fin d → ℚ) : List (Fin (d+1) → ℤ) :=
  let neg := requestMagnitudeNegative (manuscriptProxyFuel N) (paperRadius N+7) mag
  SignQueries.history (affineCommitReply neg) (roundingProgramWith M (lllShortSelector M))

/-- The implementation's two native LLL invocations have the same uniform cutoff for
all their visited affine comparisons, including their constant coordinate. -/
theorem nativeRounding_history_cutoff {d : ℕ} (N M : ℕ) (hM : 0 < M) (mag : Fin d → ℚ)
    (hm : ∀ i, 0 < mag i) (row : Fin (d+1) → ℤ) (hr : row ∈ nativeRoundingHistory N M mag)
    (hfill : paperRadius N+7+(d+1)+queryCoefficientWidth (d+1) M ≤ manuscriptProxyFuel N) :
    (2 : ℤ)^(paperRadius N+7) * (|row (Fin.last d)| + ∑ i : Fin d, |row i.castSucc|) ≤
      2^manuscriptProxyFuel N := by
  let fuel := manuscriptProxyFuel N
  let k := paperRadius N+7
  apply manuscript_rounding_query_l1 (fun i ↦ requestMagnitudeProxy fuel k (mag i)) hM _
    (lllShortSelector_correct (Nat.succ_pos _) hM) (requestMagnitudeNegative fuel k mag)
    (requestMagnitudeNegative_correct fuel k mag hm) row hr hfill

/-- Rational power registers and exact step count for any query written with an admissible
coefficient cap. Its use does not enumerate the full universe of matrix minors. -/
theorem nativeProxyPower_cost {d : ℕ} (N : ℕ) (mag : Fin d → ℚ) (hm : ∀ i, 0 < mag i)
    (a : Fin d → ℤ) (c : ℤ) (B : ℕ) (hbits : ∀ i, ratBits (mag i) ≤ B)
    (hq : (2 : ℤ)^(paperRadius N+7)*(|c|+∑ i, |a i|) ≤ 2^manuscriptProxyFuel N) :
    let fuel := manuscriptProxyFuel N
    let k := paperRadius N+7
    let data i := logProxyNumerator fuel k (mag i)
    let large := Finset.univ.filter (fun i => data i = none)
    let trace := proxyPowerTrace large (2^(k+2)) c a (fun i => (data i).getD 0) mag
    trace.2.length ≤ 2*(2*fuel+3)+2+d*(2*(fuel+3)+2) ∧
      ((∃ j, data j = none) → ∀ w ∈ trace.2, ratBits w ≤ 9+4*(4*B^2)+d*(3+(4*B)*B)) := by
  intro fuel k data large trace
  constructor
  · simpa only [Fintype.card_fin] using computedProxyProduct_steps fuel k c a mag hm le_rfl hq
  · intro hs
    simpa only [Fintype.card_fin] using
      (computedProxyProduct_registerBounds fuel k B c a mag hm hbits le_rfl hq hs).2

end Compression
end LinearProgramming
end Optimization
end OAI

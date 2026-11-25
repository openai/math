import OAI.LinearAlgebra.FiniteFourier.Feedback.FeedbackSeries
import OAI.LinearAlgebra.FiniteFourier.WeightedTransfer

/-! # The weighted transfer estimate for a binary feedback system

The input to the walk estimate is the series obtained by iterating the actual binary
gates. The rank correction uses the rational transfer of the same state equations.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace Feedback

open Polynomial
noncomputable section

variable {K O I : Type*} [Field K] [Infinite K] [Fintype O] [Fintype I] {s : ℕ}

/-- Lemma `tr:transfer` applied directly to a regular feedback system. -/
theorem weightedTransfer (F : Feedback K I O s) (hF : F.Regular) (ν : TensorValue K (O × I))
    (B : K[X]) (Q : Matrix O I K[X]) (d r : ℕ) (hB : B.eval 1 = 1)
    (hQ : ∀ o i, (Q o i).natDegree ≤ d)
    (hR : ((algebraMap K[X] (RatFunc K) B) • F.rationalTransfer -
      Q.map (algebraMap K[X] (RatFunc K))).rank ≤ r)
    {w L U : ℝ} (hw : 0 < w) (hw1 : w ≤ 1) (hL : 0 ≤ L) (hU : 0 ≤ U)
    (p : Polynomial ℝ)
    (walk : ∀ k i : ℕ, 1 ≤ k → w ^ i * ν.price k (powerCoeff (Function.uncurry F.delaySeries) k i) ≤
      p.eval (k : ℝ) * L ^ k)
    (rank : ∀ M : Matrix O I K, M.rank ≤ r → ν.price 1 (slotPower (Function.uncurry M) 1) ≤ U) :
    ν.price 1 (slotPower (Function.uncurry F.matrix) 1) ≤ U + w⁻¹ ^ d * (L + U) := by
  let φ := algebraMap K[X] (RatFunc K)
  have hden : φ F.transferDenom ≠ 0 := RatFunc.algebraMap_ne_zero F.transferDenom_ne_zero
  have corr : rationalQuotient (B • F.transferNumer - F.transferDenom • Q) F.transferDenom =
      (φ B) • F.rationalTransfer - Q.map φ := by
    ext o i
    change φ (B * F.transferNumer o i - F.transferDenom * Q o i) / φ F.transferDenom =
      φ B * (φ (F.transferNumer o i) / φ F.transferDenom) - φ (Q o i)
    rw [map_sub, map_mul, map_mul]
    field_simp [hden]
  have h0 : F.transferDenom.coeff 0 ≠ 0 := by
    rw [coeff_zero_eq_eval_zero, F.eval_zero_transferDenom]
    exact one_ne_zero
  have h1 : F.transferDenom.eval 1 ≠ 0 := by rwa [F.eval_one_transferDenom]
  have hs : quotientSeries F.transferNumer F.transferDenom = Function.uncurry F.delaySeries := by
    funext z
    exact (F.delaySeries_eq_quotient z.1 z.2).symm
  have ho : quotientAt F.transferNumer F.transferDenom 1 = F.matrix := by
    rw [← F.eval_one_rationalTransfer hF]
    ext o i
    exact (F.eval_rationalTransfer_entry h1 o i).symm
  rw [← ho]
  apply weightedCoefficientEstimate ν F.transferNumer Q F.transferDenom B h0 h1 hB d r hQ
    (corr ▸ hR) hw hw1 hL hU p _ rank
  simpa only [hs] using walk

end
end Feedback

end FiniteFourier
end LinearAlgebra
end OAI

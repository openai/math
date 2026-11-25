import OAI.LinearAlgebra.FiniteFourier.PolynomialCoefficientCost
import OAI.LinearAlgebra.FiniteFourier.RankCorrection

/-! # Weighted coefficient estimate for a rational transfer matrix

With `A = P/h`, the correction `BA-Q` has numerator `B • P - h • Q` and the same denominator.
This gives one polynomial presentation for both its Taylor expansion and its value at one.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Polynomial
open scoped BigOperators

noncomputable section

variable {K O I : Type*} [Field K] [Infinite K] [Fintype O] [Fintype I]

/-- Lemma `tr:transfer`. The walk bound is imposed on the coefficients of the actual powers of
`A=P/h`, and the correction rank is measured over the rational function field. The proof works
over any infinite field and needs only the degree bound for the polynomial matrix `Q`. -/
theorem weightedCoefficientEstimate (ν : TensorValue K (O × I))
    (P Q : Matrix O I K[X]) (h B : K[X]) (h0 : h.coeff 0 ≠ 0) (h1 : h.eval 1 ≠ 0)
    (hB : B.eval 1 = 1) (d r : ℕ) (hQ : ∀ o i, (Q o i).natDegree ≤ d)
    (hR : (rationalQuotient (B • P - h • Q) h).rank ≤ r)
    {w L U : ℝ} (hw : 0 < w) (hw1 : w ≤ 1) (hL : 0 ≤ L) (hU : 0 ≤ U)
    (p : Polynomial ℝ)
    (walk : ∀ k i : ℕ, 1 ≤ k → w ^ i * ν.price k (powerCoeff (quotientSeries P h) k i) ≤
      p.eval (k : ℝ) * L ^ k)
    (rank : ∀ M : Matrix O I K, M.rank ≤ r → ν.price 1 (slotPower (Function.uncurry M) 1) ≤ U) :
    ν.price 1 (slotPower (Function.uncurry (quotientAt P h 1)) 1) ≤ U + w⁻¹ ^ d * (L + U) := by
  classical
  let N : Matrix O I K[X] := B • P - h • Q
  let e := ∑ t : O × I, (N t.1 t.2).natDegree
  have hN (o : O) (i : I) : (N o i).natDegree ≤ e :=
    Finset.single_le_sum (s := Finset.univ) (a := (o,i)) (f := fun t : O × I => (N t.1 t.2).natDegree)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ (o, i))
  have corr := weightedBound_rationalQuotient ν N h h0 e r hN hR hw.le hw1 hU rank
  have base := weightedBound_of_walk_estimate (quotientSeries P h) p hL walk
  have hc := (base.scalarSeries hw.le hw1 hL (B : PowerSeries K)).add
    (corr.scalarSeries hw.le hw1 hU (-1 : PowerSeries K)) hw.le hL hU
  let q (z : O × I) := Q z.1 z.2
  have split₀ :
      ((fun z => (B : PowerSeries K) * quotientSeries P h z) +
        (fun z => (-1 : PowerSeries K) * quotientSeries N h z)) =
        (fun z => (q z : PowerSeries K)) := by
    funext z
    have hunit := PowerSeries.mul_inv_cancel (h : PowerSeries K) (by simpa using h0)
    change (B : PowerSeries K) * ((P z.1 z.2 : PowerSeries K) * (h : PowerSeries K)⁻¹) +
      -1 * (((B * P z.1 z.2 - h * q z : K[X]) : PowerSeries K) * (h : PowerSeries K)⁻¹) = _
    push_cast
    linear_combination (q z : PowerSeries K) * hunit
  rw [split₀] at hc
  have hq := polynomialValue_of_weightedBound ν q d (fun z => hQ z.1 z.2) hw hw1
    (add_nonneg hL hU) hc
  have hr := rank _ ((rank_quotientAt_le N h 1 h1).trans hR)
  have split₁ :
      slotPower (Function.uncurry (quotientAt P h 1)) 1 =
        slotPower (fun z => (q z).eval 1) 1 +
          slotPower (Function.uncurry (quotientAt N h 1)) 1 := by
    ext x
    simp only [slotPower, Fin.prod_univ_one, Pi.add_apply, Function.uncurry, quotientAt]
    change (P _ _).eval 1 / h.eval 1 = (q (x 0)).eval 1 +
      (B * P _ _ - h * q (x 0)).eval 1 / h.eval 1
    simp [hB, h1, sub_div, mul_div_cancel_left₀]
  rw [split₁]
  exact (ν.add _ _).trans ((add_le_add hq hr).trans_eq (add_comm _ _))

end

end FiniteFourier
end LinearAlgebra
end OAI

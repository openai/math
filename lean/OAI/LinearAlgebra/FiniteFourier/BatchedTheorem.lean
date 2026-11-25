import OAI.LinearAlgebra.FiniteFourier.BatchedUpper
import OAI.LinearAlgebra.FiniteFourier.BatchedBoundedOrders
import OAI.LinearAlgebra.FiniteFourier.BatchedProjectedList
import OAI.LinearAlgebra.FiniteFourier.BatchedQuotient
import OAI.LinearAlgebra.FiniteFourier.BatchedTimeShift
import OAI.LinearAlgebra.FiniteFourier.BatchedLargeOrders
import OAI.LinearAlgebra.FiniteFourier.RadialPlaneLaws
import OAI.LinearAlgebra.SpectralBooks.EveryField

/-! # Theorem 1.1 of *Batched Fourier transforms and the geometry of linear networks*

For large orders, delay dilation turns a joint border point into a repeated
list of inputs and outputs with one global rank budget and one global support
budget. The spectral plane over the algebraic closure rules out this list
when the state count is too small. A two-minor argument covers the remaining
orders. The cutoff is fixed before choosing the field, order or batch size.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

universe u v

/-- Lower estimate in the joint geometric border. The budgets apply to the entire
`Jn`-by-`Jn` array. Entries in off-diagonal blocks count in the same support budget. -/
def RobustBatchFourierLower : Prop :=
  ∃ c β η : ℝ, 0 < c ∧ 0 < β ∧ 0 < η ∧
    ∀ {J n : ℕ} (K : Type v) [Field K] (B : Fin J → FourierBlock.{u,v} K n),
      1 ≤ J → 2 ≤ n → ∀ S : ℕ,
      let h : ℝ := J * (n : ℝ)
      let l := Real.sqrt (Real.logb 2 n)
      JointErrorBorderAtMost (batchMatrix B) S (β * h) (η * h * (2 : ℝ) ^ (l / 8)) →
      c * h * l ≤ S

/-- The joint robust statement with exact acyclic upper and lower estimates. -/
def BatchedFourierComplexityTheorem : Prop :=
  ∃ c β η : ℝ, 0 < c ∧ 0 < β ∧ 0 < η ∧ ∀ ε : ℝ, 0 < ε → ∃ C > (0 : ℝ),
    ∀ {J n : ℕ} (K : Type v) [Field K] (B : Fin J → FourierBlock.{u,v} K n),
      1 ≤ J → 2 ≤ n →
      let h : ℝ := J * (n : ℝ)
      let l := Real.sqrt (Real.logb (2 : ℕ) n)
      let T := batchMatrix B
      (c * h * l ≤ complexity T ∧
        (complexity T : ℝ) ≤
          C * h * (1 + Real.logb (2 : ℕ) n) ^ ((1 : ℝ) / (2 : ℕ) + ε)) ∧
      ∀ S : ℕ, JointErrorBorderAtMost T S (β * h) (η * h * (↑(2 : ℕ) : ℝ) ^ (l / (8 : ℕ))) →
        c * h * l ≤ S

/-- The exact lower estimate follows by specializing the joint error to zero. -/
theorem batchedFourierComplexity_of_robustLower (lower : RobustBatchFourierLower.{u,v}) :
    BatchedFourierComplexityTheorem.{u,v} := by
  obtain ⟨c, β, η, hc, hβ, hη, lower⟩ := lower
  refine ⟨c, β, η, hc, hβ, hη, fun ε hε => ?_⟩
  obtain ⟨C, hC, upper⟩ := batchFourier_upper.{u,v} hε
  refine ⟨C, hC, ?_⟩
  intro J n K _ B hJ hn
  have robust := lower K B hJ hn
  refine ⟨⟨robust _ ?_, upper K B hn⟩, robust⟩
  exact (realizableAtMost_complexity _).geometricBorder.jointError (by positivity) (by positivity)

/-- A uniform robust bound beyond a fixed cutoff extends to every order. Both the
error fractions and the lower constant may be decreased when joining the two ranges. -/
theorem batchedFourierComplexity_of_largeOrders {N : ℕ} (hN : 2 ≤ N)
    {c β η : ℝ} (hc : 0 < c) (hβ : 0 < β) (hη : 0 < η)
    (large : ∀ {J n : ℕ} (K : Type v) [Field K] (B : Fin J → FourierBlock.{u,v} K n),
      1 ≤ J → N ≤ n → ∀ S : ℕ,
      let h : ℝ := J * (n : ℝ)
      let l := Real.sqrt (Real.logb 2 n)
      JointErrorBorderAtMost (batchMatrix B) S (β * h) (η * h * (2 : ℝ) ^ (l / 8)) →
        c * h * l ≤ S) : BatchedFourierComplexityTheorem.{u,v} := by
  apply batchedFourierComplexity_of_robustLower
  obtain ⟨c₀, β₀, η₀, hc₀, hβ₀, hη₀, small⟩ := batchFourier_bounded_orders.{u,v} N hN
  refine ⟨min c c₀, min β β₀, min η η₀, lt_min hc hc₀, lt_min hβ hβ₀, lt_min hη hη₀, ?_⟩
  intro J n K _ B hJ hn S
  dsimp only
  intro h
  by_cases hcut : N ≤ n
  · apply le_trans _ (large K B hJ hcut S (h.mono ?_ ?_))
    all_goals (gcongr; exact min_le_left ..)
  · apply le_trans _ (small K B hn (le_of_not_ge hcut) S (h.mono ?_ ?_))
    all_goals (gcongr; exact min_le_right ..)

/-- Every regular binary feedback realization is a joint border point, even
when both error budgets vanish. -/
theorem FeedbackAtMost.jointError {I O K : Type*} [Field K] [Fintype I] [Fintype O]
    {M : Matrix O I K} {S : ℕ} (h : FeedbackAtMost M S) {r t : ℝ}
    (hr : 0 ≤ r) (ht : 0 ≤ t) : JointErrorBorderAtMost M S r t :=
  h.geometricBorder.jointError hr ht

/-- Theorem 1.1. The same positive lower constant and error fractions work
for all admissible fields, group orders, batch sizes and transform directions. -/
theorem batchedFourierComplexity : BatchedFourierComplexityTheorem.{u,v} := by
  obtain ⟨N, hN, hcut⟩ := exists_batch_large_cutoff
  have hb : 0 < batchRankFraction := by unfold batchRankFraction; positivity
  apply batchedFourierComplexity_of_largeOrders hN
    (show 0 < batchRankFraction / 128 by positivity) hb (by norm_num : (0 : ℝ) < 1 / 4)
  intro J n K _ B hJ hn S
  obtain ⟨P, hP⟩ := OAI.LinearAlgebra.SpectralBooks.matrix_spectral_plane (AlgebraicClosure K)
  exact large_batch_lower (tangentPlane P) (tangentPlane_fourierPlaneLaws P hP)
    B hJ (hN.trans hn) (hcut n hn) S

end FiniteFourier
end LinearAlgebra
end OAI

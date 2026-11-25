import OAI.LinearAlgebra.FiniteFourier.BatchedAugment
import OAI.LinearAlgebra.FiniteFourier.BatchedDelayBounds
import OAI.LinearAlgebra.FiniteFourier.CharacterSaturation
import OAI.LinearAlgebra.FiniteFourier.RectangleWidth

/-! # Joint geometric-border lower bound in the large-order range -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open OAI.LinearAlgebra.SpectralBooks
noncomputable section

universe u v

def batchRankFraction : ℝ := (2:ℝ)^(-(100:ℤ)) / 400

/-- With a spectral plane over the algebraic closure, the rank and support
obstruction applies to the coalescing delay family for the entire batch. -/
theorem large_batch_lower {J n : ℕ} {K : Type v} [Field K]
    (P : SpectralPlacementPrices (AlgebraicClosure K) Plane)
    (hP : FourierPlaneLaws P)
    (B : Fin J → FourierBlock.{u,v} K n) (hJ : 1 ≤ J) (hn : 2 ≤ n)
    (hl : 1000 ≤ Real.sqrt (Real.logb 2 n)) (S : ℕ) :
    let h : ℝ := J * (n:ℝ)
    let l := Real.sqrt (Real.logb 2 n)
    JointErrorBorderAtMost (batchMatrix B) S (batchRankFraction*h)
      (1/4*h*(2:ℝ)^(l/8)) →
    batchRankFraction/128*h*l ≤ S := by
  intro h l he
  by_contra! hs
  let d := batchDelays l
  have hd : 0 < d := batchDelays_pos hl
  let _ : Nonempty (Fin (J*d)) := Fin.pos_iff_nonempty.mp (Nat.mul_pos hJ hd)
  let t := 1/4*h*(2:ℝ)^(l/8)
  let T := ((n:ℝ)*J)*d + repeatSupportBudget (n*J) d t
  have hT : 0 ≤ T := by unfold T repeatSupportBudget t h; positivity
  have hr : ((S + ⌊batchRankFraction*h⌋₊ * d : ℕ):ℝ) ≤
      (2:ℝ)^(-(100:ℤ)) * (↑(J*d) * (n:ℝ)) / 200 := by
    apply (batch_delay_rank_budget hl (show 0 ≤ h by unfold h; positivity)
      (show 0 ≤ batchRankFraction by unfold batchRankFraction; positivity) hs).trans
    unfold batchRankFraction h d
    push_cast
    exact le_of_eq (by ring)
  have ht : T ≤ ↑(J*d) * (n:ℝ) * (2:ℝ)^(l/8) := by
    have hbound := batch_delay_support_budget hl (n*J)
    dsimp only at hbound
    push_cast at hbound
    simpa only [T, t, h, d, Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using hbound
  exact batch_rank_sparse_obstruction P hP.flat
    (fun _ hL => rectangle_diagonal_price P hP.flat hL.le (by norm_num))
    (fun _ _ _ had e _ hL => enumerated_fourier_rectanglePrice P hP had e hL.le)
    (algebraMap K (AlgebraicClosure K))
    (fun jd : Fin (J*d) => B (finProdFinEquiv.symm jd).1) hn hl _ T hT hr ht
    (jointError_augmented_repeat B he d)

open Filter in
theorem exists_batch_large_cutoff :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n → 1000 ≤ Real.sqrt (Real.logb 2 n) := by
  have h : Tendsto (fun n : ℕ => Real.sqrt (Real.logb 2 n)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp ((Real.tendsto_logb_atTop (by norm_num : (1:ℝ) < 2)).comp
      tendsto_natCast_atTop_atTop)
  obtain ⟨N,hN⟩ := eventually_atTop.1 (h.eventually (eventually_ge_atTop 1000))
  exact ⟨max 2 N, le_max_left _ _, fun n hn => hN n ((le_max_right _ _).trans hn)⟩

end
end FiniteFourier
end LinearAlgebra
end OAI

import OAI.Optimization.LinearProgramming.PriceGame.TrialExecutionMarket
import Mathlib.Algebra.GCDMonoid.Finset

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace TrialExecution

open States.Mass

/-- The least common unit for the input flow weights. -/
def weightDenominator {n : ℕ} (L : Fin n → ℚ) : ℕ :=
  Finset.univ.lcm (fun i => (L i).den)

theorem weightDenominator_pos {n : ℕ} (L : Fin n → ℚ) : 0 < weightDenominator L :=
  Nat.pos_of_ne_zero (Finset.lcm_ne_zero_iff.mpr (fun i _ => (L i).den_ne_zero))

theorem weightDenominator_dvd {n : ℕ} (L : Fin n → ℚ) {Q : ℕ}
    (hQ : ∀ i, (L i).den ∣ Q) : weightDenominator L ∣ Q :=
  Finset.lcm_dvd fun i _ => hQ i

theorem den_dvd_weightDenominator {n : ℕ} (L : Fin n → ℚ) (i : Fin n) :
    (L i).den ∣ weightDenominator L :=
  Finset.dvd_lcm (Finset.mem_univ i)

private theorem rat_den_of_nat_quot_dvd (a d : ℕ) : ((a : ℚ) / d).den ∣ d := by
  apply Int.natCast_dvd_natCast.mp
  simpa [Rat.divInt_eq_div] using Rat.den_dvd (a : ℤ) (d : ℤ)

/-- Use the least common, rather than a potentially redundant, flow unit. -/
def computeAtCommonWeightUnit : FinMarket := fun pos L available c =>
  Market.computeWithDenominator pos L available c (weightDenominator L)

theorem computeAtCommonWeightUnit_correct : FinMarketCorrect computeAtCommonWeightUnit :=
  fun pos L available c hL =>
    (Market.computeWithDenominator_spec pos L available c (weightDenominator L)
      (weightDenominator_pos L) hL (den_dvd_weightDenominator L)).1

/-- The actual trial adapter with canonical integral flow units. -/
def marketSolverAtCommonWeightUnit {N ne : ℕ} (experts : Fin ne → Expert N) : MarketSolver experts :=
  marketSolverOfFin computeAtCommonWeightUnit computeAtCommonWeightUnit_correct experts

/-- The input weights' common denominators, the bids' common denominators, and the
size estimate on cleared prices all transport across the coordinate addressing scheme. -/
theorem marketSolverAtCommonWeightUnit_bounds {N ne : ℕ} (experts : Fin ne → Expert N)
    (l : ℕ) (history : History N) (L : Weights ne) (hL : ∀ e, 0 ≤ L e) :
    let result := marketSolverAtCommonWeightUnit experts l history L hL
    (∀ Q : ℕ, (∀ e, (L e).den ∣ Q) → ∀ e o, (L e * result.fractions e o).den ∣ Q) ∧
    (∀ D : ℕ, (∀ e i, (experts e).accepts l i = true →
      ∃ z : ℤ, (D : ℚ) * (experts e).intercept history i = z) →
      ∀ i, ∃ z : ℤ, (D : ℚ) * result.prices i = z) ∧
    (∀ B : ℚ, 0 ≤ B → (∀ e i, (experts e).accepts l i = true →
      |(experts e).intercept history i| ≤ B) →
      ∀ i, |result.prices i| ≤ 2 * ((ne + N * 2 ^ l + 1 : ℕ) : ℚ) * B) := by
  let v := vertexEquivFin N l
  let pos (e : Fin ne) := (experts e).skeleton.positive
  let available (e : Fin ne) (i : Fin (N * 2 ^ l)) := (experts e).accepts l (v.symm i)
  let bids (e : Fin ne) (i : Fin (N * 2 ^ l)) := (experts e).intercept history (v.symm i)
  let out := Market.computeWithDenominator pos L available bids (weightDenominator L)
  obtain ⟨_, hmass, hpr, hsize⟩ := Market.computeWithDenominator_spec pos L available bids
    (weightDenominator L) (weightDenominator_pos L) hL (den_dvd_weightDenominator L)
  refine ⟨?_, ?_, ?_⟩
  · intro Q hQ e o
    change (L e * out.2 e (o.map v)).den ∣ Q
    obtain ⟨a, ha⟩ := hmass e (o.map v)
    change L e * out.2 e (o.map v) = _ at ha
    rw [ha]
    exact (rat_den_of_nat_quot_dvd a _).trans (weightDenominator_dvd L hQ)
  · intro D hd i
    exact hpr D (fun e j h => hd e (v.symm j) h) (v i)
  · intro B hb h i
    exact hsize B hb (fun e j hj => h e (v.symm j) hj) (v i)

end TrialExecution
end PriceGame
end LinearProgramming
end Optimization
end OAI

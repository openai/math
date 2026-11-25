import OAI.Optimization.LinearProgramming.PriceGame.MarketAugmentSolver

/-! Exact optimality of the integer solution against real-valued comparison flows. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Market
namespace Augment

open scoped BigOperators

variable {E G : Type*} [Fintype E] [Fintype G]

/-- Dotting reduced-cost inequalities against a real feasible flow also bounds its value.
The candidate flow may use fractional amounts even though the returned allocation is integral. -/
theorem real_flow_optimal {pos : E → Bool} {accepts : E → G → Prop} {c : E → G → ℚ}
    {f : E → Option G → ℕ} {qty : E → ℕ} {p : E → ℚ} {π : Option G → ℚ}
    (hf : Optimum.Feasible pos qty accepts f) (hp : ResidualPotentials pos accepts c f p π)
    (g : E → Option G → ℝ) (nonneg : ∀ e o, 0 ≤ g e o)
    (used : ∀ e o, 0 < g e o → eligible accepts e o)
    (row : ∀ e, ∑ o, g e o = qty e)
    (good : ∀ i, ∑ e, (side pos e : ℝ) * g e (some i) = 0) :
    (∑ e, ∑ o, (bid c e o : ℝ) * g e o) ≤ (Optimum.value c f : ℝ) := by
  have cancel : ∑ e, ∑ o, ((side pos e : ℝ) * g e o) * ((π o : ℝ) - π none) = 0 := by
    rw [Finset.sum_comm]; apply Finset.sum_eq_zero
    intro o _
    cases o with
    | none => simp
    | some i => rw [← Finset.sum_mul, good, zero_mul]
  have linear : (∑ e, ∑ o, (side pos e : ℝ) * ((p e:ℝ) - π o) * g e o) =
      ∑ e, (side pos e : ℝ) * ((p e : ℝ) - π none) * qty e := by
    calc
      _ = ∑ e, ∑ o, ((side pos e : ℝ)*((p e:ℝ)-π none)*g e o -
           ((side pos e : ℝ)*g e o)*((π o:ℝ)-π none)) := by
        apply Finset.sum_congr rfl; intro e _
        apply Finset.sum_congr rfl; intro o _; ring
      _ = _ := by
        simp only [Finset.sum_sub_distrib, cancel, sub_zero]
        apply Finset.sum_congr rfl; intro e _
        rw [← Finset.mul_sum, row]
  have achieved : (∑ e, side pos e * (p e - π none) * (qty e : ℚ)) ≤ Optimum.value c f := by
    rw [← OptimumDual.total_drop hf p π]
    apply Finset.sum_le_sum; intro e _
    apply Finset.sum_le_sum; intro o _
    by_cases h : f e o = 0
    · simp [h, Optimum.arcWeight]
    · exact mul_le_mul_of_nonneg_right (hp.backward e o (Nat.pos_of_ne_zero h)) (Nat.cast_nonneg _)
  calc
    _ ≤ ∑ e, ∑ o, (side pos e : ℝ)*((p e:ℝ)-π o)*g e o := by
      apply Finset.sum_le_sum; intro e _
      apply Finset.sum_le_sum; intro o _
      rcases (nonneg e o).eq_or_lt with h|h
      · simp [← h]
      · apply mul_le_mul_of_nonneg_right _ h.le
        exact_mod_cast hp.forward e o (used e o h)
    _ = _ := linear
    _ ≤ _ := by exact_mod_cast achieved

/-- The bit-scaling algorithm returns an integral global optimum of the real flow polytope. -/
theorem Input.solve_real_optimal {m g : ℕ} (I : Input m g) (qty : Fin m → ℕ)
    (f : Fin m → Option (Fin g) → ℝ) (hn : ∀ e o, 0 ≤ f e o)
    (allowed : ∀ e o, 0 < f e o → eligible I.accepts e o)
    (row : ∀ e, ∑ o, f e o = qty e)
    (balance : ∀ i, ∑ e, (side I.positive e : ℝ) * f e (some i) = 0) :
    (∑ e, ∑ o, (bid I.intercept e o : ℝ) * f e o) ≤
      (Optimum.value I.intercept (I.solve qty).flow : ℝ) :=
  real_flow_optimal (I.solve_spec qty).feasible (I.solve_spec qty).residual f hn allowed row balance

end Augment
end Market
end PriceGame
end LinearProgramming
end Optimization
end OAI

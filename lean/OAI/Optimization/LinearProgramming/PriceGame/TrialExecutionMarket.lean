import OAI.Optimization.LinearProgramming.PriceGame.TrialExecutionTypes
import OAI.Optimization.LinearProgramming.PriceGame.VertexEncoding
import OAI.Optimization.LinearProgramming.PriceGame.MarketCompute

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace TrialExecution

open States.Mass

/-- Finite-array interface for an executable market clearing algorithm. -/
abbrev FinMarket := ∀ {e g : ℕ}, (Fin e → Bool) → (Fin e → ℚ) →
  (Fin e → Fin g → Bool) → (Fin e → Fin g → ℚ) →
  (Fin g → ℚ) × (Fin e → Option (Fin g) → ℚ)

def FinMarketCorrect (compute : FinMarket) : Prop :=
  ∀ {e g : ℕ} (pos : Fin e → Bool) (L : Fin e → ℚ) (accepts : Fin e → Fin g → Bool)
    (c : Fin e → Fin g → ℚ), (∀ k, 0 ≤ L k) →
    Market.Balanced pos L (fun k i => accepts k i = true) c
      (compute pos L accepts c).1 (compute pos L accepts c).2

/-- Transport a balanced price vector and all its maximizing allocations along a
bijection of goods. The outside option is fixed. -/
theorem balanced_reindex {E I J : Type*} [Fintype E] [Fintype I] [Fintype J]
    (v : I ≃ J) (pos : E → Bool) (L : E → ℚ) (accepts : E → I → Prop)
    (c : E → I → ℚ) (y : J → ℚ) (f : E → Option J → ℚ)
    (h : Market.Balanced pos L (fun e j => accepts e (v.symm j)) (fun e j => c e (v.symm j)) y f) :
    Market.Balanced pos L accepts c (fun i => y (v i))
      (fun e o => f e (o.map v)) := by
  have eligible (e : E) (o : Option I) :
      Market.eligible (fun e j => accepts e (v.symm j)) e (o.map v) ↔ Market.eligible accepts e o := by
    cases o <;> simp [Market.eligible]
  have score (e : E) (o : Option I) :
      Market.score pos (fun e j => c e (v.symm j)) y e (o.map v) =
        Market.score pos c (fun i => y (v i)) e o := by
    cases o <;> simp [Market.score]
  refine ⟨fun e o => h.nonneg e (o.map v), ?_, ?_, ?_, fun i => h.clears (v i)⟩
  · intro e
    exact (v.optionCongr.sum_comp (f e)).trans (h.unit e)
  · exact fun e o ho => (eligible e o).mp (h.allowed e (o.map v) ho)
  · intro e o ho u ho' hu
    rw [← score e o, ← score e u]
    exact h.maximizes e (o.map v) ho (u.map v) ((eligible e o).mpr ho') ((eligible e u).mpr hu)

/-- The trial builds the market directly from the supplied expert list, path
history, and incoming rational weights. Coordinate addresses use mixed radix. -/
def marketSolverOfFin (compute : FinMarket) (correct : FinMarketCorrect compute)
    {N ne : ℕ} (experts : Fin ne → Expert N) : MarketSolver experts := fun l history L hL =>
  let v := vertexEquivFin N l
  let pos (e : Fin ne) := (experts e).skeleton.positive
  let available (e : Fin ne) (i : Fin (N * 2 ^ l)) := (experts e).accepts l (v.symm i)
  let bids (e : Fin ne) (i : Fin (N * 2 ^ l)) := (experts e).intercept history (v.symm i)
  let result := compute pos L available bids
  { prices := fun i => result.1 (v i)
    fractions := fun e o => result.2 e (o.map v)
    balanced := balanced_reindex v pos L (fun e i => (experts e).accepts l i = true)
      (fun e i => (experts e).intercept history i) result.1 result.2
      (correct pos L available bids hL) }

/-- Concrete deterministic solver: binary-scaled integral transshipment followed by residual path potentials. -/
def computedMarketSolver {N ne : ℕ} (experts : Fin ne → Expert N) : MarketSolver experts :=
  marketSolverOfFin (fun pos L available c => Market.compute pos L available c)
    (fun pos L available c hL => Market.compute_balanced pos L available c hL) experts

end TrialExecution
end PriceGame
end LinearProgramming
end Optimization
end OAI

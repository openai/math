import OAI.Optimization.LinearProgramming.PriceGame.TrialExecutionChildren
import OAI.Optimization.LinearProgramming.PriceGame.TrialExecutionAssembleFacts
import OAI.Optimization.LinearProgramming.PriceGame.ChargingState
import OAI.Optimization.LinearProgramming.PriceGame.StatesChargingScores

/-! # The two charging groups in the actual recursive price-game schedule -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace TrialExecution

open Charging States.Mass

variable {N ne k l R : ℕ} {anchor : Fin N}

def chargeProbes {experts : Fin ne → Expert N} {w : Weights ne}
    (s : NodeRun experts w (2*k+1) l) (j : Calls k) : Prices N l := (s.val (probeIndex j)).data.baseline

def chargeChildren {experts : Fin ne → Expert N} {w : Weights ne}
    (s : NodeRun experts w (2*k+1) l) (b : Sum (Calls k) (Calls k)) : Prices N (l+1) :=
  (s.val (groupedIndex (2*k+1) b)).child.prices

variable (hidden : Hidden N R anchor) (experts : Fin ne → Expert N) (solve : MarketSolver experts)
    (w : Weights ne) (hw : ∀ e, 0 ≤ w e) (hist : History N)
    (path : States.Path (Fin N) (Vertex N l))
    (child : (y : Prices N l) → (dw : Weights ne) → (∀ e, 0 ≤ dw e) →
      Computation N (Certified (N:=N) (r:=2*k+1) (l:=l+1) dw))
    (s : NodeRun experts w (2*k+1) l)
    (reachable : ∀ j : Fin (2*(2*k+1)), Computation.Reaches hidden
      (executeStep experts solve w hw hist path child j («prefix» s.val j)) ⟨s.val j,s.property j⟩)

include hidden solve hw hist path child reachable

/-- A probe receives its own quote. Every final call receives the coordinatewise
odd median of the same first-group prices. -/
theorem reached_callBaseline (b : Sum (Calls k) (Calls k)) :
    (s.val (groupedIndex (2*k+1) b)).data.baseline = callBaseline (chargeProbes s) b := by
  cases b with
  | inl b => rfl
  | inr b =>
    change (s.val (finalIndex b)).data.baseline = fun i => oddMedian fun j => chargeProbes s j i
    rw [reached_final_baseline hidden experts solve w hw hist path child s b (reachable _)]
    funext i
    exact median_odd _

/-- This is the price used by the failed-node charging induction, pointwise equal
to the price returned by the executable assembly. -/
theorem reached_assembled_prices :
    (assemble experts hist w s).val.prices = fun i =>
      oddMedian (fun b : Calls k =>
        States.parentPrices (callBaseline (chargeProbes s) (.inr b)) (chargeChildren s (.inr b)) i) := by
  funext i
  rw [assemble_price_odd]
  apply congrArg oddMedian
  funext b
  have hm := (reached_child hidden experts solve w hw hist path child s (finalIndex b) (reachable _)).2.2
  have hb := reached_callBaseline hidden experts solve w hw hist path child s reachable (.inr b)
  change (s.val (finalIndex b)).data.baseline = _ at hb
  rw [hm,hb]
  rfl

end TrialExecution
end PriceGame
end LinearProgramming
end Optimization
end OAI

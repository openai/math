import OAI.Optimization.LinearProgramming.PriceGame.TrialExecutionPackets
import OAI.Optimization.LinearProgramming.PriceGame.StatesFeedback

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace TrialExecution

open States.Mass Moment Finset

variable {N ne r l : ℕ}

/-- Compute the next adaptive child. Earlier results are immutable; the second group
always uses the same median of the first group's market prices. -/
def executeStep (experts : Fin ne → Expert N) (solve : MarketSolver experts)
    (w : Weights ne) (hw : ∀ e, 0 ≤ w e) (history : History N)
    (path : States.Path (Fin N) (Vertex N l))
    (child : (y : Prices N l) → (dw : Weights ne) → (∀ e, 0 ≤ dw e) →
      Computation N (Certified (N:=N) (r:=r) (l:=l+1) dw))
    (j : ℕ) (xs : Fin j → Call N ne r l) : Computation N {c // StepOK experts w xs c} :=
  let dw := incomingDeep experts w xs
  let hdw := incomingDeep_nonneg experts w hw xs
  if hj : j < r then
    let A := solve l history (incomingLocal experts w xs) (incomingLocal_nonneg experts w hw xs)
    (child A.prices dw hdw).bind fun ch =>
      (States.feedbackAll path A.prices ch.val.prices).map (probeReturn experts w history xs hj A ch)
  else
    let y : Prices N l := fun i => median fun t : Fin r =>
      (xs ⟨t.val, lt_of_lt_of_le t.isLt (Nat.le_of_not_gt hj)⟩).data.baseline i
    (child y dw hdw).map (finalReturn experts w xs (Nat.le_of_not_gt hj) y)

theorem executeStep_height_le (experts : Fin ne → Expert N) (solve : MarketSolver experts)
    (w : Weights ne) (hw : ∀ e, 0 ≤ w e) (history : History N)
    (path : States.Path (Fin N) (Vertex N l))
    (child : (y : Prices N l) → (dw : Weights ne) → (∀ e, 0 ≤ dw e) →
      Computation N (Certified (N:=N) (r:=r) (l:=l+1) dw))
    (K : ℕ) (hk : ∀ y dw hdw, (child y dw hdw).height ≤ K)
    (j : ℕ) (xs : Fin j → Call N ne r l) :
    (executeStep experts solve w hw history path child j xs).height ≤ K + Fintype.card (Vertex N l) := by
  unfold executeStep
  dsimp only
  split
  · apply le_trans (Computation.height_bind_le _ _ (Fintype.card (Vertex N l)) ?_)
    · exact Nat.add_le_add_right (hk _ _ _) _
    · intro ch
      rw [Computation.height_map]
      exact States.feedbackAll_height _ _ _
  · rw [Computation.height_map]
    exact (hk _ _ _).trans (Nat.le_add_right _ _)

end TrialExecution
end PriceGame
end LinearProgramming
end Optimization
end OAI

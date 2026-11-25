import OAI.Computability.BorderVNP.CrossingFactorChecker
import OAI.Computability.BorderVNP.CrossingFactorBudget
import OAI.Computability.BorderVNP.CrossingKernelFrame

/-!
# Actual signed verifiers for every iterated crossing stage

This instantiates the terminal and mode decoder with the verified normally ordered
fermionic kernel. Both its number of private choices and its gate count are bounded
by one polynomial independently of the selected terminal assignment or orientation.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing.FusionStage

open Signed

/-- The signed local table computation, with its own private choices and formal
sum of integer path signs. -/
noncomputable def checker {q H : ℕ} (w : WireStates H q) (E : ℕ) (reverse left : Bool) :
    Checker w E reverse left where
  guesses := KernelFrame.width left (E+H) w.weight
  frame := KernelWrapper.frame w reverse left (KernelFrame.gates left (E+H) w.weight)
  correct := KernelWrapper.frame_sum w reverse left _ (KernelFrame.gates_sum left)

/-- Uniform polynomial bounds on the two resources of the concrete local checker. -/
theorem checker_budget {q H : ℕ} (w : WireStates H q) (E : ℕ) (reverse left : Bool) :
    (checker w E reverse left).guesses ≤ (q+H+E+2)^210 ∧
      (checker w E reverse left).frame.size ≤ (q+H+E+2)^210 :=
  factorChecker_budget w.weight_le (KernelFrame.gates_size left (E+H) w.weight)
    (KernelFrame.width_le left (E+H) w.weight) (KernelWrapper.frame_size w reverse left _)

/-- A single polynomial in the alphabet cardinality controls every stage of the fusion. -/
theorem checker_stage_budget {q H D m : ℕ} (w : WireStates H q) (E : ℕ) (reverse left : Bool)
    (hD : D ≤ m) (hm : m ≤ q) (hH : 2*H ≤ q) (hE : E ≤ D*H) :
    (checker w E reverse left).guesses ≤ (q+2)^420 ∧
      (checker w E reverse left).frame.size ≤ (q+2)^420 := by
  have h := checker_budget w E reverse left
  exact ⟨factorChecker_stage_budget hD hm hH hE h.1, factorChecker_stage_budget hD hm hH hE h.2⟩

end Crossing.FusionStage

end BorderVNP
end Computability
end OAI

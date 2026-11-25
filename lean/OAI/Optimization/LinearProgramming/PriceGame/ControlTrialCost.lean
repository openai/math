import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialCore
import OAI.Optimization.LinearProgramming.PriceGame.TrialQueryTraces
import OAI.Optimization.LinearProgramming.PriceGame.TrialExecutionComplexity

/-! The polynomial number of first-order control instructions, with each query
counted separately. Arithmetic inside a phase, and time spent replaying the local
feedback scan, are independent costs from these control instructions. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Trial

universe u

open States.Mass TrialExecution

theorem ticks_le_node_count (calls d : ℕ) :
    nodeTicks calls d + 3 ≤ 5 * Complexity.nodeCount calls d := by
  induction d with
  | zero => norm_num [nodeTicks, Complexity.nodeCount]
  | succ d ih =>
    simp only [nodeTicks, Complexity.nodeCount]
    have he := Nat.mul_le_mul_left calls ih
    calc
      2 + calls * (nodeTicks calls d + 3) + 3 ≤ 5 + calls * (5*Complexity.nodeCount calls d) := by omega
      _ = _ := by ring

theorem Emits.length_le_height {N : ℕ} {α : Type u} {p : Computation N α} {tr a}
    (e : Emits p tr a) : tr.length ≤ p.height := by
  induction e with
  | pure => exact le_rfl
  | ask b e ih =>
    simp only [List.length_cons, Computation.height, Nat.add_le_add_iff_right]
    cases b
    · exact ih.trans (Nat.le_max_left _ _)
    · exact ih.trans (Nat.le_max_right _ _)

/-- Price-trial stack ticks for every possible transcript, independent of hidden values. -/
theorem trial_ticks_polynomial {N ne : ℕ} (hN : 0 < N) (R : ℕ) (experts : Fin ne → Expert N)
    (solve : MarketSolver experts) (w : Weights ne) (hw : ∀ i, 0 ≤ w i) {tr out}
    (e : Emits (run R experts solve w hw) tr out) :
    nodeTicks (2*Complexity.probes) (depth N) + tr.length ≤
      5*(2*N)^602 + (2*(N+1))^605 := by
  have h1 := ticks_le_node_count (2*Complexity.probes) (depth N)
  have h2 := Nat.mul_le_mul_left 5 (Complexity.trial_nodes_le N hN)
  exact Nat.add_le_add (by omega) (e.length_le_height.trans (run_height_polynomial R experts solve w hw))

end Trial
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI

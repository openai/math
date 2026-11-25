import OAI.Optimization.LinearProgramming.PriceGame.MarketAugmentMachineRun
import OAI.Optimization.LinearProgramming.PriceGame.MarketAugmentMachineBridge
import OAI.Optimization.LinearProgramming.PriceGame.MarketSolverBounds
import OAI.Optimization.LinearProgramming.PriceGame.MarketAugmentReal

/-! End-to-end refinement of the uniform binary transshipment program. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Market
namespace Augment
namespace Machine

open ExactQuantumFactoring.BitStackProgram NumberBounds
variable {m g : ℕ}

/-- Serialize each state of a genuine augmentation sequence. All old-bank grid hypotheses
needed at the next unit follow from the already executed prefix. -/
theorem fold_simulates (I : Input m g) (D : ℕ) (hD : 0 < D)
    (hc : ∀ e i, OnGrid D (I.intercept e i)) (ops : List (Option (Fin m))) :
    (ops.map ScheduleMachine.actionNumber).foldl (fun s a => action (a,s)) (packEnv I D I.initial) =
      packEnv I D (ops.foldl (operation Input.double I.unit) I.initial) := by
  induction ops using List.reverseRecOn with
  | nil => rfl
  | append_singleton l a ih =>
    simp only [List.map_append,List.map_singleton,List.foldl_append,List.foldl_cons,List.foldl_nil,ih]
    let s := l.foldl (operation Input.double I.unit) I.initial
    have h := run_bound I hc l (initial_bound I D hc)
    have step := action_simulates I D s a hD (fun e i _ => hc e i) h.expert_grid h.option_grid
    cases a <;> exact step

/-- The machine's output is the complete canonical coding of the integral optimum and
carried residual-potential banks, including zero supplies, ties, and the dummy option. -/
theorem execute_exact (I : Input m g) (qty : Fin m → ℕ) (D : ℕ) (hD : 0 < D)
    (hc : ∀ e i, OnGrid D (I.intercept e i)) :
    execute ((List.finRange m).map qty,packEnv I D I.initial) = (packEnv I D (I.solve qty)).2 := by
  let q := (List.finRange m).map qty
  let K := (listCode Nat.bits q).length
  have hk : Input.bits qty ≤ K := Finset.sup_le fun i _ => Nat.size_le.mpr (ScheduleMachine.padding_fits qty i)
  change ((ScheduleMachine.actionStream q).foldl (fun s a => action (a,s)) (packEnv I D I.initial)).2 = _
  rw [ScheduleMachine.actionStream_correct,fold_simulates I D hD hc]
  have st : (schedule K qty).foldl (operation Input.double I.unit) I.initial = I.solve qty :=
    solveWithWidth_eq_of_le I qty K hk
  rw [st]

/-- One deployed oracle-free machine, with polynomial running time in its encoded input
length, computes the same optimal flow as binary transshipment. -/
theorem computes_solution (oracle : OracleSpec.WordOracle) (I : Input m g) (qty : Fin m → ℕ)
    (D : ℕ) (hD : 0 < D) (hc : ∀ e i, OnGrid D (I.intercept e i)) :
    let z : SolverInput := ((List.finRange m).map qty,packEnv I D I.initial)
    (OracleSpec.BitCode.deploy solveP).ComputesWithin oracle (solverInputCode z)
      (3*solveP.bound.eval (solverInputCode z).length+2*(solverInputCode z).length+2)
      (fun hist bits => hist=[] ∧ bits=dynCode (packEnv I D (I.solve qty)).2) := by
  have run := solve_deploy oracle ((List.finRange m).map qty,packEnv I D I.initial)
  simpa only [execute_exact I qty D hD hc] using run

/-- A polynomial-time integral optimal transshipment. The same flow maximizes the
objective over arbitrary feasible real shipments. Both feasibility and the residual
dual are certified for the state whose entire encoding is written by the machine. -/
theorem polynomial_transshipment (oracle : OracleSpec.WordOracle) (I : Input m g) (qty : Fin m → ℕ)
    (D : ℕ) (hD : 0 < D) (hc : ∀ e i, OnGrid D (I.intercept e i)) :
    let z : SolverInput := ((List.finRange m).map qty,packEnv I D I.initial)
    ∃ s : State m g, I.Invariant s qty ∧
      (∀ f : Fin m → Option (Fin g) → ℝ, (∀ e o, 0 ≤ f e o) →
        (∀ e o, 0 < f e o → eligible I.accepts e o) → (∀ e, ∑ o, f e o = qty e) →
        (∀ i, ∑ e, (side I.positive e : ℝ)*f e (some i) = 0) →
        (∑ e, ∑ o, (bid I.intercept e o : ℝ)*f e o) ≤ (Optimum.value I.intercept s.flow : ℝ)) ∧
      (OracleSpec.BitCode.deploy solveP).ComputesWithin oracle (solverInputCode z)
        (3*solveP.bound.eval (solverInputCode z).length+2*(solverInputCode z).length+2)
        (fun hist bits => hist=[] ∧ bits=dynCode (packEnv I D s).2) :=
  ⟨I.solve qty,I.solve_spec qty,I.solve_real_optimal qty,computes_solution oracle I qty D hD hc⟩

end Machine
end Augment
end Market
end PriceGame
end LinearProgramming
end Optimization
end OAI

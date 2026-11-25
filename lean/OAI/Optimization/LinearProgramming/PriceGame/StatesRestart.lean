import OAI.Optimization.LinearProgramming.PriceGame.StatesRounding
import OAI.Optimization.LinearProgramming.Recovery.Restart

/-! # Restarting an extremal-sign learner on a geometric label service

After every restart, a completed epoch may use its own extension of the compressed
costs. Only its range and winning sign are shared with the other epochs (§2.3).
-/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace States
namespace Restart

open OAI.Optimization.LinearProgramming.Recovery
open OAI.Optimization.LinearProgramming.PriceGame.States.Rounding

variable {N : ℕ} {anchor : Fin N}

/-- Execute a single operation of a price-query tree. The branches retain the actual
adaptive dependence on previous answers. -/
def step : Tree N → Move (Tree N) (Query N) Bool
  | .result a => .done a
  | .ask q children => .query q (children false) (children true)

theorem bounded_of_height (t : Tree N) {fuel : ℕ} (hf : t.height < fuel) :
    Bounded step fuel t := by
  induction t generalizing fuel with
  | result a =>
    cases fuel with
    | zero => omega
    | succ k => exact True.intro
  | ask q children ih =>
    cases fuel with
    | zero => omega
    | succ k =>
      simp only [Tree.height] at hf
      exact ⟨ih false (by omega), ih true (by omega)⟩

/-- Validity of the returned bits on the one observed log suffices for a legal path;
counterfactual answers at other prices need no single preselected extension. -/
theorem reaches_of_learnerRun {R : ℕ} (hidden : Hidden N R anchor) (t : Tree N)
    {log : List (Event (Query N))} {answer : Bool} (hr : LearnerRun step t log answer)
    (valid : ∀ q b, (q, some b) ∈ log → hidden.Forced q → b = hidden.positive) :
    Tree.Reaches hidden t answer := by
  induction t generalizing log answer with
  | result a =>
    cases hr with
    | done he => cases he; exact .result a
    | work he _ => cases he
    | query b he _ => cases he
  | ask q kids ih =>
    cases hr with
    | done he => cases he
    | work he _ => cases he
    | query b he tail =>
      cases he
      apply Tree.Reaches.ask (valid q b (by simp))
      cases b <;>
        exact ih _ tail (fun q' b' mem => valid q' b' (List.mem_cons_of_mem _ mem))

/-- Predicate promised by the geometric label test: a target within two units of the
winning-side minimum is labeled by that sign. -/
def nearTwo (d : Instance N anchor) (q : Query N) : Prop :=
  q.index ∈ d.active ∧ ∀ j ∈ d.active, d.cost q.index + d.signedPrice (q.prices q.index : ℝ) ≤
    d.cost j + d.signedPrice (q.prices j : ℝ) + 2

/-- If each restart-free service transcript admits a common geometric cost assignment,
the actual bounded restart simulation recovers the winning sign. The cost assignment
can depend on that transcript, including its final query. -/
theorem recover_sign_with_clock {State : Type*} (serve : State → Query N → Reply State)
    (initial : State) (winning : Bool) (B restarts : ℕ)
    (learner : Tree N) (maxQueries : ℕ) (hClock : learner.height ≤ maxQueries)
    (sound : ∀ h : Hidden N B anchor, Tree.Correct h learner)
    (common : ∀ {s t} (past log : List (Event (Query N))), ServicePath serve initial past s →
      ServicePath serve s log t → restartCount log = 0 →
      ∃ d : Instance N anchor, d.range = B ∧ d.ε = 1 ∧ d.positive = winning ∧
        ∀ q b, (q, some b) ∈ log → nearTwo d q → b = winning)
    (cap : ∀ {t} (log : List (Event (Query N))), ServicePath serve initial log t →
      restartCount log ≤ restarts) :
    let result := Recovery.run step serve (maxQueries + 1) learner (restarts + 1) initial
    result.value = some winning ∧ result.log.length ≤ (restarts + 1) * (maxQueries + 1) := by
  let Witness := {d : Instance N anchor // d.range = B ∧ d.ε = 1 ∧ d.positive = winning}
  let admissible (w : Witness) (q : Query N) (b : Bool) := nearTwo w.val q → b = winning
  apply restart_recovery step serve (maxQueries + 1) restarts learner initial winning admissible
    (bounded_of_height learner (Nat.lt_succ_of_le hClock)) _ _ cap
  · intro s t past log reachable epoch noRestart
    obtain ⟨d, hr, hu, hs, hw⟩ := common past log reachable epoch noRestart
    exact ⟨⟨d, hr, hu, hs⟩, hw⟩
  · intro log answer run witness
    obtain ⟨⟨d, hr, hu, hs⟩, responses⟩ := witness
    have ok : Tree.Correct d.rounded learner := by
      subst B
      exact sound d.rounded
    have trace := reaches_of_learnerRun d.rounded learner run (by
      intro q b mem forced
      exact (responses q b mem (forced_geometric d hu q forced)).trans hs.symm)
    exact (ok answer trace).trans hs

/-- The intrinsic tree-height specialization of the public-clock recovery theorem. -/
theorem recover_sign {State : Type*} (serve : State → Query N → Reply State)
    (initial : State) (winning : Bool) (B restarts : ℕ)
    (learner : Tree N) (sound : ∀ h : Hidden N B anchor, Tree.Correct h learner)
    (common : ∀ {s t} (past log : List (Event (Query N))), ServicePath serve initial past s →
      ServicePath serve s log t → restartCount log = 0 →
      ∃ d : Instance N anchor, d.range = B ∧ d.ε = 1 ∧ d.positive = winning ∧
        ∀ q b, (q, some b) ∈ log → nearTwo d q → b = winning)
    (cap : ∀ {t} (log : List (Event (Query N))), ServicePath serve initial log t →
      restartCount log ≤ restarts) :
    let result := Recovery.run step serve (learner.height + 1) learner (restarts + 1) initial
    result.value = some winning ∧ result.log.length ≤ (restarts + 1) * (learner.height + 1) :=
  recover_sign_with_clock serve initial winning B restarts learner learner.height le_rfl sound common cap

end Restart
end States
end PriceGame
end LinearProgramming
end Optimization
end OAI

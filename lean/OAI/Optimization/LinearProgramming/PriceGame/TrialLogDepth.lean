import OAI.Optimization.LinearProgramming.PriceGame.TrialExecutionSize

/-! Levels of every price observation found in the output of an arbitrary branch. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace TrialExecution

open States.Mass

private def validLevels {N : ℕ} (top : ℕ) (ps : List (Probe N)) : Prop :=
  ∀ p ∈ ps, p.level < top

private theorem nodeLog_validLevels {N ne r l top : ℕ} (hl : l < top) (history : History N)
    (xs : Fin (2*r) → Call N ne r l) (hc : ∀ j, validLevels top (xs j).child.log) :
    validLevels top (nodeLog history xs) := by
  intro p hp
  obtain ⟨sub, hs, hm⟩ := List.mem_flatten.mp hp
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hs
  split at hm
  · rcases List.mem_cons.mp hm with rfl | hm
    · exact hl
    · exact hc j p hm
  · exact hc j p hm

private theorem executeStep_validLevels {N ne r l : ℕ} (top : ℕ)
    (experts : Fin ne → Expert N) (solve : MarketSolver experts)
    (w : Weights ne) (hw : ∀ e, 0 ≤ w e) (history : History N)
    (path : States.Path (Fin N) (Vertex N l))
    (child : (y : Prices N l) → (dw : Weights ne) → (∀ e, 0 ≤ dw e) →
      Computation N (Certified (N:=N) (r:=r) (l:=l+1) dw))
    (hc : ∀ y dw hdw, Computation.AllOutputs (fun ch => validLevels top ch.val.log) (child y dw hdw))
    (j : ℕ) (xs : Fin j → Call N ne r l) :
    Computation.AllOutputs (fun c => validLevels top c.val.child.log)
      (executeStep experts solve w hw history path child j xs) := by
  unfold executeStep
  dsimp only
  split
  · apply (hc _ _ _).bind
    intro ch hch
    apply Computation.AllOutputs.map_of_forall
    exact fun _ => hch
  · apply (hc _ _ _).map
    exact fun _ hch => hch

theorem execute_log_depth {N ne : ℕ} (r R top : ℕ) (experts : Fin ne → Expert N)
    (solve : MarketSolver experts) (fuel l : ℕ) (hlen : l+fuel ≤ top)
    (path : States.Path (Fin N) (Vertex N l)) (history : History N)
    (w : Weights ne) (hw : ∀ e, 0 ≤ w e) :
    Computation.AllOutputs (fun out => ∀ p ∈ out.val.log, p.level < top)
      (execute r R experts solve fuel l path history w hw) := by
  induction fuel generalizing l history w with
  | zero => exact .pure (by simp [leafOutput])
  | succ d ih =>
    rw [execute]
    let child := fun (y : Prices N l) (dw : Weights ne) (hdw : ∀ e, 0 ≤ dw e) =>
      execute r R experts solve d (l+1) (.extend path y (vertexDecidableEq N l)) (history.push l y) dw hdw
    let p := fun (j : ℕ) (xs : Fin j → Call N ne r l) (c : Call N ne r l) => StepOK experts w xs c
    let step := executeStep experts solve w hw history path child
    change Computation.AllOutputs _ ((runSchedule p step (2*r)).map (assemble experts history w))
    apply (runSchedule_all p step (fun c => validLevels top c.child.log) (2*r) ?_).map
    · intro s hs
      exact nodeLog_validLevels (by omega) history s.val hs
    · intro j _ xs
      apply executeStep_validLevels
      intro y dw hdw
      exact ih (l+1) (by omega) _ (history.push l y) dw hdw

theorem runReference_log_depth {N ne : ℕ} (R : ℕ) (experts : Fin ne → Expert N)
    (w : Weights ne) (hw : ∀ e, 0 ≤ w e) :
    Computation.AllOutputs (fun out => ∀ p ∈ out.val.log, p.level < depth N)
      (runReference R experts w hw) := by
  unfold runReference run
  generalize Moment.probes = r
  exact execute_log_depth r R _ experts _ _ _ (by omega) _ _ _ _

end TrialExecution
end PriceGame
end LinearProgramming
end Optimization
end OAI

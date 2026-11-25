import OAI.Optimization.LinearProgramming.PriceGame.TrialExecutionChildren

/-! Structural induction on actual executions of the trial. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace TrialExecution

open States.Mass Moment

variable {N ne r R : ℕ} {anchor : Fin N}

/-- The continuation called at a non-leaf, exposed for statements about recorded child runs. -/
def nextCall (r R : ℕ) (experts : Fin ne → Expert N) (solve : MarketSolver experts)
    (fuel l : ℕ) (path : States.Path (Fin N) (Vertex N l)) (history : History N)
    (y : Prices N l) (dw : Weights ne) (hdw : ∀ e, 0 ≤ dw e) :=
  execute r R experts solve fuel (l+1) (.extend path y (vertexDecidableEq N l))
    (history.push l y) dw hdw

/-- A full induction principle in which each child's induction hypothesis uses the
returned price path, and each oracle reply remains witnessed by an actual run. -/
theorem execute_induct (h : Hidden N R anchor) (experts : Fin ne → Expert N)
    (solve : MarketSolver experts)
    (P : (fuel l : ℕ) → States.Path (Fin N) (Vertex N l) → History N → Output N ne r l → Prop)
    (hbase : ∀ l path history w, P 0 l path history (leafOutput (N:=N) r R l w).val)
    (hnode : ∀ fuel l path history w (hw : ∀ e, 0 ≤ w e) (s : NodeRun experts w r l),
      (∀ j : Fin (2*r), Computation.Reaches h
          (executeStep experts solve w hw history path (nextCall r R experts solve fuel l path history)
            j («prefix» s.val j)) ⟨s.val j, s.property j⟩) →
      (∀ j : Fin (2*r), P fuel (l+1) (.extend path (s.val j).data.baseline (vertexDecidableEq N l))
        (history.push l (s.val j).data.baseline) (s.val j).child) →
      P (fuel+1) l path history (assemble experts history w s).val)
    (fuel l : ℕ) (path : States.Path (Fin N) (Vertex N l)) (history : History N)
    (w : Weights ne) (hw : ∀ e, 0 ≤ w e) (out : Certified (N:=N) (r:=r) (l:=l) w)
    (hr : Computation.Reaches h (execute r R experts solve fuel l path history w hw) out) :
    P fuel l path history out.val := by
  induction fuel generalizing l history w with
  | zero =>
    rw [execute, Computation.reaches_pure_iff] at hr
    subst out
    exact hbase _ _ _ _
  | succ fuel ih =>
    obtain ⟨s,rfl,hsteps⟩ := execute_node_reaches h r R experts solve fuel l path history w hw out hr
    apply hnode fuel l path history w hw s hsteps
    intro j
    have hit := (reached_child h experts solve w hw history path _
      s j (hsteps j)).1
    exact ih _ _ _ _ _ (scheduleChild experts w s j) hit

end TrialExecution
end PriceGame
end LinearProgramming
end Optimization
end OAI

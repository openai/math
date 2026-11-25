import OAI.Optimization.LinearProgramming.PriceGame.TrialExecutionReaches

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace TrialExecution

open States.Mass Moment

variable {N ne r l : ℕ}

/-- The actual child output at the incoming weights certified by its prefix. -/
def scheduleChild (experts : Fin ne → Expert N) (w : Weights ne)
    (s : NodeRun experts w r l) (j : Fin (2*r)) :
    Certified (N:=N) (r:=r) (l:=l+1) (incomingDeep experts w («prefix» s.val j)) :=
  ⟨(s.val j).child, (s.property j).admissible⟩

/-- Both branches are run by the same continuation at their stored baseline and incoming weights. -/
theorem reached_child {R : ℕ} {anchor : Fin N} (h : Hidden N R anchor) (experts : Fin ne → Expert N)
    (solve : MarketSolver experts) (w : Weights ne) (hw : ∀ e, 0 ≤ w e) (history : History N)
    (path : States.Path (Fin N) (Vertex N l))
    (child : (y : Prices N l) → (dw : Weights ne) → (∀ e, 0 ≤ dw e) →
      Computation N (Certified (N:=N) (r:=r) (l:=l+1) dw))
    (s : NodeRun experts w r l) (j : Fin (2*r))
    (hj : Computation.Reaches h
      (executeStep experts solve w hw history path child j («prefix» s.val j))
        ⟨s.val j,s.property j⟩) :
    let xs := «prefix» s.val j
    Computation.Reaches h (child (s.val j).data.baseline (incomingDeep experts w xs)
      (incomingDeep_nonneg experts w hw xs)) (scheduleChild experts w s j) ∧
    (s.val j).data.childPrices = (s.val j).child.prices ∧
    (s.val j).data.mapped = States.parentPrices (s.val j).data.baseline (s.val j).child.prices := by
  intro xs
  by_cases hp : j.val < r
  · obtain ⟨ch, hch, hs, _, hb, hm, hc⟩ :=
      executeStep_probe_reaches h experts solve w hw history path child j xs hp _ hj
    have hchild : scheduleChild experts w s j = ch := Subtype.ext hs
    refine ⟨?_, hc.trans (congrArg Output.prices hs.symm), ?_⟩
    · rw [hchild, hb]
      exact hch
    · rw [hb, hs]
      exact hm
  · obtain ⟨ch, hch, hs, hb, hm, hc⟩ :=
      executeStep_final_reaches h experts solve w hw history path child j xs (Nat.le_of_not_gt hp) _ hj
    have hchild : scheduleChild experts w s j = ch := Subtype.ext hs
    refine ⟨?_, hc.trans (congrArg Output.prices hs.symm), ?_⟩
    · rw [hchild, hb]
      exact hch
    · rw [hb, hs]
      exact hm

theorem reached_probe_feedback {R : ℕ} {anchor : Fin N} (h : Hidden N R anchor)
    (experts : Fin ne → Expert N) (solve : MarketSolver experts) (w : Weights ne)
    (hw : ∀ e, 0 ≤ w e) (history : History N) (path : States.Path (Fin N) (Vertex N l))
    (child : (y : Prices N l) → (dw : Weights ne) → (∀ e, 0 ≤ dw e) →
      Computation N (Certified (N:=N) (r:=r) (l:=l+1) dw))
    (s : NodeRun experts w r l) (j : Fin r)
    (hj : Computation.Reaches h
      (executeStep experts solve w hw history path child (probeIndex j) («prefix» s.val (probeIndex j)))
      ⟨s.val (probeIndex j),s.property (probeIndex j)⟩) :
    let c := s.val (probeIndex j)
    Computation.Reaches h (States.feedbackAll path c.data.baseline c.child.prices) c.data.labels := by
  intro c
  obtain ⟨ch, _, hs, hfb, hb, _, _⟩ := executeStep_probe_reaches h experts solve w hw history path
    child (probeIndex j) («prefix» s.val (probeIndex j)) j.isLt _ hj
  change Computation.Reaches h (States.feedbackAll path (s.val (probeIndex j)).data.baseline
    (s.val (probeIndex j)).child.prices) _
  rw [hb, hs]
  exact hfb

theorem priorMedian_finalIndex (xs : Fin (2*r) → Call N ne r l) (b : Fin r) :
    priorMedian («prefix» xs (finalIndex b)) (by simp [finalIndex]) =
      fun i => median fun t : Fin r => (xs (probeIndex t)).data.baseline i := by
  rfl

theorem reached_final_baseline {R : ℕ} {anchor : Fin N} (h : Hidden N R anchor)
    (experts : Fin ne → Expert N) (solve : MarketSolver experts) (w : Weights ne)
    (hw : ∀ e, 0 ≤ w e) (history : History N) (path : States.Path (Fin N) (Vertex N l))
    (child : (y : Prices N l) → (dw : Weights ne) → (∀ e, 0 ≤ dw e) →
      Computation N (Certified (N:=N) (r:=r) (l:=l+1) dw))
    (s : NodeRun experts w r l) (b : Fin r)
    (hj : Computation.Reaches h
      (executeStep experts solve w hw history path child (finalIndex b) («prefix» s.val (finalIndex b)))
      ⟨s.val (finalIndex b),s.property (finalIndex b)⟩) :
    (s.val (finalIndex b)).data.baseline =
      fun i => median fun t : Fin r => (s.val (probeIndex t)).data.baseline i := by
  obtain ⟨_, _, _, hb, _, _⟩ := executeStep_final_reaches h experts solve w hw history path
    child (finalIndex b) («prefix» s.val (finalIndex b)) (by simp [finalIndex]) _ hj
  exact hb.trans (priorMedian_finalIndex s.val b)

end TrialExecution
end PriceGame
end LinearProgramming
end Optimization
end OAI

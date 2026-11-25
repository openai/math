import OAI.Optimization.LinearProgramming.PriceGame.TrialExecution

/-! Decomposing a public execution recovers each recursive computation at the actual
weights and each designated feedback query at the actual returned child price. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace TrialExecution

open States.Mass Moment

variable {N ne r l bound : ℕ} {anchor : Fin N}

/-- The common baseline used by every final call selects the coordinatewise median
of the original first group of market quotes. -/
def priorMedian {j : ℕ} (xs : Fin j → Call N ne r l) (hj : r ≤ j) : Prices N l :=
  fun i => median fun t : Fin r => (xs ⟨t.val, lt_of_lt_of_le t.isLt hj⟩).data.baseline i

theorem executeStep_probe_reaches (hidden : Hidden N bound anchor) (experts : Fin ne → Expert N)
    (solve : MarketSolver experts) (w : Weights ne) (hw : ∀ e, 0 ≤ w e) (history : History N)
    (path : States.Path (Fin N) (Vertex N l))
    (child : (y : Prices N l) → (dw : Weights ne) → (∀ e, 0 ≤ dw e) →
      Computation N (Certified (N:=N) (r:=r) (l:=l+1) dw))
    (j : ℕ) (xs : Fin j → Call N ne r l) (hj : j < r)
    (c : {c // StepOK experts w xs c})
    (hr : Computation.Reaches hidden (executeStep experts solve w hw history path child j xs) c) :
    let A := solve l history (incomingLocal experts w xs) (incomingLocal_nonneg experts w hw xs)
    ∃ ch : Certified (N:=N) (r:=r) (l:=l+1) (incomingDeep experts w xs),
      Computation.Reaches hidden (child A.prices (incomingDeep experts w xs)
        (incomingDeep_nonneg experts w hw xs)) ch ∧ c.val.child = ch.val ∧
      Computation.Reaches hidden (States.feedbackAll path A.prices ch.val.prices) c.val.data.labels ∧
      c.val.data.baseline = A.prices ∧ c.val.data.mapped = States.parentPrices A.prices ch.val.prices ∧
      c.val.data.childPrices = ch.val.prices := by
  intro A
  simp only [executeStep, dite_eq_left hj, Computation.reaches_bind_iff] at hr
  obtain ⟨ch, hch, hz⟩ := hr
  obtain ⟨z, hret, rfl⟩ := (Computation.reaches_map_iff _ _ _ _).mp hz
  exact ⟨ch, hch, rfl, hret, rfl, rfl, rfl⟩

theorem executeStep_final_reaches (hidden : Hidden N bound anchor) (experts : Fin ne → Expert N)
    (solve : MarketSolver experts) (w : Weights ne) (hw : ∀ e, 0 ≤ w e) (history : History N)
    (path : States.Path (Fin N) (Vertex N l))
    (child : (y : Prices N l) → (dw : Weights ne) → (∀ e, 0 ≤ dw e) →
      Computation N (Certified (N:=N) (r:=r) (l:=l+1) dw))
    (j : ℕ) (xs : Fin j → Call N ne r l) (hj : r ≤ j)
    (c : {c // StepOK experts w xs c})
    (hr : Computation.Reaches hidden (executeStep experts solve w hw history path child j xs) c) :
    ∃ ch : Certified (N:=N) (r:=r) (l:=l+1) (incomingDeep experts w xs),
      Computation.Reaches hidden (child (priorMedian xs hj) (incomingDeep experts w xs)
        (incomingDeep_nonneg experts w hw xs)) ch ∧ c.val.child = ch.val ∧
      c.val.data.baseline = priorMedian xs hj ∧
      c.val.data.mapped = States.parentPrices (priorMedian xs hj) ch.val.prices ∧
      c.val.data.childPrices = ch.val.prices := by
  simp only [executeStep, dite_eq_right (Nat.not_lt.mpr hj)] at hr
  obtain ⟨ch, hch, rfl⟩ := (Computation.reaches_map_iff _ _ _ _).mp hr
  exact ⟨ch, hch, rfl, rfl, rfl, rfl⟩

theorem execute_node_reaches (hidden : Hidden N bound anchor)
    (r R : ℕ) (experts : Fin ne → Expert N) (solve : MarketSolver experts) (fuel l : ℕ)
    (path : States.Path (Fin N) (Vertex N l)) (history : History N)
    (w : Weights ne) (hw : ∀ e, 0 ≤ w e) (out : Certified (N:=N) (r:=r) (l:=l) w)
    (hr : Computation.Reaches hidden (execute r R experts solve (fuel+1) l path history w hw) out) :
    ∃ s : NodeRun experts w r l, out = assemble experts history w s ∧
      ∀ j : Fin (2*r), Computation.Reaches hidden
        (executeStep experts solve w hw history path
          (fun y dw hdw => execute r R experts solve fuel (l+1) (.extend path y (vertexDecidableEq N l))
            (history.push l y) dw hdw)
          j («prefix» s.val j))
        ⟨s.val j, s.property j⟩ := by
  rw [execute, Computation.reaches_map_iff] at hr
  obtain ⟨s, hs, rfl⟩ := hr
  exact ⟨s, rfl, (runSchedule_reaches_iff _ _ _ _ _).mp hs⟩

end TrialExecution
end PriceGame
end LinearProgramming
end Optimization
end OAI

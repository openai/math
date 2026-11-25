import OAI.Optimization.LinearProgramming.PriceGame.TrialExecutionAssemble
import OAI.Optimization.LinearProgramming.PriceGame.TrialExecutionStep
import OAI.Optimization.LinearProgramming.PriceGame.MomentScoreBound

/-! Section 6 reads the actual maximizing allocation, its baseline and its feedback
from the receipts produced by the two groups of scheduled calls. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace TrialExecution

open States.Mass Moment Finset

variable {N ne r l : ℕ}

/-- The whole market answer for a recorded probe, including its outside-option mass.
The clearing conditions concern exactly the roster and weights before this call. -/
structure RecordedProbe (roster : Fin ne → Expert N) (before : Weights ne)
    (event : RoundData N ne l) (snap : MarketSnapshot N ne l) : Prop where
  stored : event.market = some snap
  experts_eq : snap.experts = roster
  weights_eq : snap.weights = before
  prices_eq : event.baseline = snap.answer.prices
  alloc_eq : event.alloc = fun e i => snap.answer.fractions e (some i)
  gain_eq : ∀ e, event.gain[e] = gainQ event.alloc (sides roster) (fun i => labelSign (event.labels i)) e
  balanced : Market.Balanced (fun e => (roster e).skeleton.positive) before
    (fun e i => (roster e).accepts l i = true) (fun e i => (roster e).intercept snap.history i)
    event.baseline snap.answer.fractions

theorem RecordedProbe.maximizes {roster : Fin ne → Expert N} {before : Weights ne}
    {event : RoundData N ne l} {snap : MarketSnapshot N ne l}
    (rec : RecordedProbe roster before event snap) (e : Fin ne) (o o' : Option (Vertex N l))
    (hu : 0 < snap.answer.fractions e o)
    (hel : Market.eligible (fun e i => (roster e).accepts l i = true) e o') :
    Market.score (fun e => (roster e).skeleton.positive) (fun e i => (roster e).intercept snap.history i)
      event.baseline e o' ≤
    Market.score (fun e => (roster e).skeleton.positive) (fun e i => (roster e).intercept snap.history i)
      event.baseline e o :=
  rec.balanced.maximizes e o hu o' (rec.balanced.allowed e o hu) hel

theorem probe_market_receipt (experts : Fin ne → Expert N) (w : Weights ne)
    (run : NodeRun experts w r l) (j : Fin r) :
    ∃ S, RecordedProbe experts (incomingLocal experts w («prefix» run.val (probeIndex j)))
      (run.val (probeIndex j)).data S := by
  have ok := run.property (probeIndex j)
  obtain ⟨S, hS, he, hw⟩ := ok.probeMarket j.isLt
  obtain ⟨hp, hf⟩ := (run.val (probeIndex j)).data.represents S hS
  refine ⟨S, ⟨hS, he, hw, hp, hf, ok.gain_eq, ?_⟩⟩
  rw [hp]
  simpa only [he, hw] using S.answer.balanced

theorem final_market_none (experts : Fin ne → Expert N) (w : Weights ne)
    (run : NodeRun experts w r l) (j : Fin r) :
    (run.val (finalIndex j)).data.market = none :=
  (run.property (finalIndex j)).finalMarket (Nat.le_add_right _ _)

/-- The snapshot at an actual probe has the same ancestor history and fractions
as the market instance that was solved. -/
theorem probeReturn_snapshot {j : ℕ} (experts : Fin ne → Expert N) (w : Weights ne)
    (history : History N) (xs : Fin j → Call N ne r l) (hj : j < r)
    (A : MarketAnswer experts l history (incomingLocal experts w xs))
    (ch : Certified (N := N) (r := r) (l := l+1) (incomingDeep experts w xs))
    (label : Vertex N l → Bool) :
    let c := (probeReturn experts w history xs hj A ch label).val
    c.data.market = some ⟨experts, history, incomingLocal experts w xs, A⟩ ∧
      c.data.baseline = A.prices ∧ c.data.alloc = (fun e i => A.fractions e (some i)) ∧
      c.data.labels = label ∧ c.data.childPrices = ch.val.prices ∧
      c.data.mapped = States.parentPrices A.prices ch.val.prices :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩


/-- Designated feedback and the child oracle may be adversarial. Every reachable
first-group call still stores the exact market computed before either oracle was read. -/
theorem executeStep_probe_stores_market {R : ℕ} {anchor : Fin N} (hidden : Hidden N R anchor)
    (experts : Fin ne → Expert N) (solve : MarketSolver experts)
    (w : Weights ne) (hw : ∀ e, 0 ≤ w e) (history : History N)
    (path : States.Path (Fin N) (Vertex N l))
    (child : (y : Prices N l) → (dw : Weights ne) → (∀ e, 0 ≤ dw e) →
      Computation N (Certified (N := N) (r := r) (l := l+1) dw))
    {j : ℕ} (xs : Fin j → Call N ne r l) (hj : j < r) (c : {c // StepOK experts w xs c})
    (hc : Computation.Reaches hidden (executeStep experts solve w hw history path child j xs) c) :
    c.val.data.market = some ⟨experts, history, incomingLocal experts w xs,
      solve l history (incomingLocal experts w xs) (incomingLocal_nonneg experts w hw xs)⟩ := by
  unfold executeStep at hc
  simp only [dite_eq_left hj] at hc
  obtain ⟨ch, _, hafter⟩ := (Computation.reaches_bind_iff _ _ _ _).mp hc
  obtain ⟨labels, _, eqc⟩ := (Computation.reaches_map_iff _ _ _ _).mp hafter
  rw [← eqc]
  rfl

theorem finalReturn_data {j : ℕ} (experts : Fin ne → Expert N) (w : Weights ne)
    (xs : Fin j → Call N ne r l) (hj : r ≤ j) (y : Prices N l)
    (ch : Certified (N := N) (r := r) (l := l+1) (incomingDeep experts w xs)) :
    let c := (finalReturn experts w xs hj y ch).val
    c.data.market = none ∧ c.data.baseline = y ∧ c.data.childPrices = ch.val.prices ∧
      c.data.mapped = States.parentPrices y ch.val.prices :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem assemble_receipt (experts : Fin ne → Expert N) (history : History N) (w : Weights ne)
    (run : NodeRun experts w r l) :
    (assemble experts history w run).val.receipt =
      .node l (fun j => (run.val j).data) (fun j => (run.val j).child.receipt) := rfl

theorem assemble_price_odd {k : ℕ} (experts : Fin ne → Expert N) (history : History N)
    (w : Weights ne) (run : NodeRun experts w (2*k+1) l) (i : Vertex N l) :
    (assemble experts history w run).val.prices i =
      Charging.oddMedian (fun j : Fin (2*k+1) => (run.val (finalIndex j)).data.mapped i) := by
  change median (fun j : Fin (2*k+1) => (run.val (finalIndex j)).data.mapped i) = _
  exact median_odd (k := k) _

theorem assemble_height_le (experts : Fin ne → Expert N) (history : History N) (w : Weights ne)
    (run : NodeRun experts w r l) (d : ℕ) (h : ∀ j, (run.val j).child.trace.height ≤ d) :
    (assemble experts history w run).val.trace.height ≤ d + 1 :=
  Nat.succ_le_succ (Finset.sup_le fun j _ => h j)

/-- Every first-group market observation carries its exact ancestor history
and the very prices used for that call. -/
theorem assemble_probe_mem_log (experts : Fin ne → Expert N) (history : History N) (w : Weights ne)
    (run : NodeRun experts w r l) (j : Fin r) :
    ⟨l, (run.val (probeIndex j)).data.baseline, history⟩ ∈
      (assemble experts history w run).val.log :=
  probe_mem_nodeLog history run.val j

theorem assemble_child_log_subset (experts : Fin ne → Expert N) (history : History N) (w : Weights ne)
    (run : NodeRun experts w r l) (j : Fin (2*r)) {p : Probe N} (hp : p ∈ (run.val j).child.log) :
    p ∈ (assemble experts history w run).val.log :=
  childLog_subset_nodeLog history run.val j hp


/-- The charging argument can look up the market, the ancestor history actually used
to form its bids, and the matching observation retained for representative refinement. -/
theorem reached_probe_receipt {R : ℕ} {anchor : Fin N} (hidden : Hidden N R anchor)
    (experts : Fin ne → Expert N) (solve : MarketSolver experts)
    (w : Weights ne) (hw : ∀ e, 0 ≤ w e) (history : History N)
    (path : States.Path (Fin N) (Vertex N l))
    (child : (y : Prices N l) → (dw : Weights ne) → (∀ e, 0 ≤ dw e) →
      Computation N (Certified (N := N) (r := r) (l := l+1) dw))
    (run : NodeRun experts w r l)
    (hr : Computation.Reaches hidden
      (runSchedule (fun j xs c => @StepOK N ne r l j experts w xs c)
        (executeStep experts solve w hw history path child) (2*r)) run)
    (j : Fin r) :
    ∃ S, RecordedProbe experts (incomingLocal experts w («prefix» run.val (probeIndex j)))
            (run.val (probeIndex j)).data S ∧
      S.history = history ∧
      ⟨l, (run.val (probeIndex j)).data.baseline, S.history⟩ ∈
        (assemble experts history w run).val.log := by
  obtain ⟨S, rec⟩ := probe_market_receipt experts w run j
  have hstep := (runSchedule_reaches_iff hidden _ _ (2*r) run).mp hr (probeIndex j)
  have hm := executeStep_probe_stores_market hidden experts solve w hw history path child
    («prefix» run.val (probeIndex j)) j.isLt ⟨_, run.property (probeIndex j)⟩ hstep
  have hS := Option.some.inj (rec.stored.symm.trans hm)
  have hHist : S.history = history := congrArg MarketSnapshot.history hS
  exact ⟨S, rec, hHist, hHist.symm ▸ assemble_probe_mem_log experts history w run j⟩

end TrialExecution
end PriceGame
end LinearProgramming
end Optimization
end OAI

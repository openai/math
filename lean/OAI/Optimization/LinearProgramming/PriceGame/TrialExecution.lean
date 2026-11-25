import OAI.Optimization.LinearProgramming.PriceGame.TrialExecutionStep
import OAI.Optimization.LinearProgramming.PriceGame.TrialExecutionAssemble
import OAI.Optimization.LinearProgramming.PriceGame.TrialExecutionMarketBounds

/-! The recursive price trial uses only public baselines, expert data, and individual
designated root queries. The certificate stored beside every output erases on compilation. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace TrialExecution

open States.Mass Moment Finset

variable {N ne r : ℕ}

def leafOutput (r R l : ℕ) (w : Weights ne) : Certified (N:=N) (r:=r) (l:=l) w :=
  ⟨{
    prices := fun i => if weight N l true i ≤ 1 then (R : ℚ) + 1 else -((R : ℚ) + 1)
    trace := .leaf
    receipt := .leaf l
    scores := Vector.replicate ne 0
    scores_eq := by intro e; simp [Trial.score]
    log := [] }, True.intro⟩

theorem leafOutput_prices (r R : ℕ) (w : Weights ne) :
    (leafOutput (N:=N) r R (depth N) w).val.prices = leafPrice N ((R : ℚ) + 1) := rfl

/-- Execute the first and second groups sequentially. The short remaining-depth
counter is public, and the recursive callback extends just the current price path. -/
def execute (r R : ℕ) (experts : Fin ne → Expert N) (solve : MarketSolver experts) :
    (fuel l : ℕ) → States.Path (Fin N) (Vertex N l) → History N →
    (w : Weights ne) → (∀ e, 0 ≤ w e) → Computation N (Certified (N:=N) (r:=r) (l:=l) w)
  | 0, l, _, _, w, _ => .pure (leafOutput r R l w)
  | fuel + 1, l, path, history, w, hw =>
    let child := fun (y : Prices N l) (dw : Weights ne) (hdw : ∀ e, 0 ≤ dw e) =>
      execute r R experts solve fuel (l + 1) (.extend path y (vertexDecidableEq N l))
        (history.push l y) dw hdw
    let p := fun (j : ℕ) (xs : Fin j → Call N ne r l) (c : Call N ne r l) => StepOK experts w xs c
    (runSchedule p (executeStep experts solve w hw history path child) (2 * r)).map
      (assemble experts history w)

/-- Start an actual trial on the original coordinates with the paper's branch count. -/
def run (R : ℕ) (experts : Fin ne → Expert N) (solve : MarketSolver experts)
    (w : Weights ne) (hw : ∀ e, 0 ≤ w e) : Computation N (Certified (N:=N) (r:=probes) (l:=0) w) :=
  execute probes R experts solve (depth N) 0 .root (fun _ _ => 0) w hw

/-- The concrete deterministic trial clears each market by binary-scaling integral
transshipment, using the least common denominator of its current weights. -/
def runReference (R : ℕ) (experts : Fin ne → Expert N)
    (w : Weights ne) (hw : ∀ e, 0 ≤ w e) : Computation N (Certified (N:=N) (r:=probes) (l:=0) w) :=
  run R experts (marketSolverAtCommonWeightUnit experts) w hw

/-- A public bound for the complete number of designated queries, including
the repeated queries needed when the median leaves a price unchanged. -/
def queryBound (N r : ℕ) : (fuel level : ℕ) → ℕ
  | 0, _ => 0
  | fuel + 1, l => 2*r*(queryBound N r fuel (l+1) + N*2^l)

theorem execute_height_le (r R : ℕ) (experts : Fin ne → Expert N) (solve : MarketSolver experts)
    (fuel l : ℕ) (path : States.Path (Fin N) (Vertex N l)) (history : History N)
    (w : Weights ne) (hw : ∀ e, 0 ≤ w e) :
    (execute r R experts solve fuel l path history w hw).height ≤ queryBound N r fuel l := by
  induction fuel generalizing l history w with
  | zero => rfl
  | succ fuel ih =>
    rw [execute, Computation.height_map, queryBound]
    apply runSchedule_height_le
    intro j _ xs
    have he := executeStep_height_le experts solve w hw history path
      (fun y dw hdw => execute r R experts solve fuel (l+1) (.extend path y (vertexDecidableEq N l))
        (history.push l y) dw hdw)
      (queryBound N r fuel (l+1)) (fun y => ih (l+1) _ (history.push l y)) j xs
    simpa only [card_vertices, Nat.mul_comm (2 ^ l) N] using he

theorem run_height_le (R : ℕ) (experts : Fin ne → Expert N) (solve : MarketSolver experts)
    (w : Weights ne) (hw : ∀ e, 0 ≤ w e) :
    (run R experts solve w hw).height ≤ queryBound N probes (depth N) 0 :=
  execute_height_le ..

theorem cached_moment {l : ℕ} (w : Weights ne) (hw : ∀ e, 0 ≤ w e)
    (out : Certified (N:=N) (r:=probes) (l:=l) w) :
    (∑ e : Fin ne, (w e : ℝ) * 2 ^ out.val.scores[e]) ≤ (2 : ℝ) ^ tau * ∑ e, (w e : ℝ) := by
  have hnn (e : Fin ne) : (0 : ℝ) ≤ w e := Rat.cast_nonneg.mpr (hw e)
  calc
    _ = ∑ e : Fin ne, (w e : ℝ) * 2 ^ out.val.trace.score scaleQ sigmaQ e :=
      sum_congr rfl fun e _ => by rw [out.val.scores_eq]
    _ ≤ _ := Trial.moment out.val.trace (fun e => (w e : ℝ)) hnn out.property

/-- Score control holds on the actual cached output, even for an arbitrary sequence
of history-dependent and inconsistent labels. -/
theorem run_moment (R : ℕ) (experts : Fin ne → Expert N) (solve : MarketSolver experts)
    (w : Weights ne) (hw : ∀ e, 0 ≤ w e) (reply : List (Query N × Bool) → Query N → Bool)
    (history : List (Query N × Bool)) :
    let out := (run R experts solve w hw).run reply history
    (∑ e : Fin ne, (w e : ℝ) * 2 ^ out.val.scores[e]) ≤ (2 : ℝ) ^ tau * ∑ e, (w e : ℝ) := by
  intro out
  exact cached_moment w hw out

end TrialExecution
end PriceGame
end LinearProgramming
end Optimization
end OAI

import OAI.Optimization.LinearProgramming.PriceGame.Experts
import OAI.Optimization.LinearProgramming.PriceGame.Market
import OAI.Optimization.LinearProgramming.PriceGame.MomentRational
import OAI.Optimization.LinearProgramming.PriceGame.StatesOracle
import OAI.Optimization.LinearProgramming.PriceGame.Charging

/-! Public records and snapshots for a recursive price-game trial. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace TrialExecution

open States.Mass Moment Finset

abbrev Prices (N l : ℕ) := Vertex N l → ℚ
abbrev Weights (ne : ℕ) := Fin ne → ℚ

/-- Median with multiplicities. The zero default is used only at arity zero. -/
def median {n : ℕ} (f : Fin n → ℚ) : ℚ :=
  if h : 0 < n then f (Tuple.sort f ⟨n / 2, by omega⟩) else 0

theorem median_odd {k : ℕ} (f : Fin (2 * k + 1) → ℚ) : median f = Charging.oddMedian f := by
  have h : 0 < 2*k+1 := by omega
  simp only [median, dite_eq_left h, Charging.oddMedian]
  apply congrArg f
  apply congrArg (Tuple.sort f)
  apply Fin.ext
  change (2 * k + 1) / 2 = k
  omega

def mask {N ne : ℕ} (experts : Fin ne → Expert N) (l : ℕ) (e : Fin ne) : Bool :=
  (experts e).isLocal l

def sides {N ne : ℕ} (experts : Fin ne → Expert N) (e : Fin ne) : ℚ :=
  Market.side (fun e => (experts e).skeleton.positive) e

theorem sides_abs {N ne : ℕ} (experts : Fin ne → Expert N) (e : Fin ne) : |sides experts e| = 1 := by
  simp only [sides, Market.side]
  split <;> norm_num

def labelSign (b : Bool) : ℚ := if b then 1 else -1

@[simp] theorem labelSign_abs (b : Bool) : |labelSign b| = 1 := by cases b <;> norm_num [labelSign]

/-- One clearing market, including its chosen optimizing allocation for the outside option. -/
structure MarketAnswer {N ne : ℕ} (experts : Fin ne → Expert N) (l : ℕ) (history : History N)
    (L : Weights ne) where
  prices : Prices N l
  fractions : Fin ne → Option (Vertex N l) → ℚ
  balanced : Market.Balanced (fun e => (experts e).skeleton.positive) L
    (fun e i => (experts e).accepts l i = true) (fun e i => (experts e).intercept history i)
    prices fractions

/-- Only the first group asks this oracle. The price procedure, its weights and
every queried coordinate are public. -/
abbrev MarketSolver {N ne : ℕ} (experts : Fin ne → Expert N) :=
  ∀ (l : ℕ) (history : History N) (L : Weights ne), (∀ e, 0 ≤ L e) → MarketAnswer experts l history L

/-- The original clearing market, preserved so that the charging proof can inspect
the allocation to the outside option and the maximizing inequalities. -/
structure MarketSnapshot (N ne l : ℕ) where
  experts : Fin ne → Expert N
  history : History N
  weights : Weights ne
  answer : MarketAnswer experts l history weights

/-- Each call stores the public quantities used in the charging argument. At a final
call `alloc`, `gain` are zero and `labels` is ignored. -/
structure RoundData (N ne l : ℕ) where
  baseline : Prices N l
  mapped : Prices N l
  childPrices : Prices N (l + 1)
  alloc : Fin ne → Vertex N l → ℚ
  labels : Vertex N l → Bool
  gain : Vector ℚ ne
  bounded : ∀ e : Fin ne, |gain[e]| ≤ 1
  market : Option (MarketSnapshot N ne l)
  represents : ∀ S, market = some S → baseline = S.answer.prices ∧
    alloc = fun e i => S.answer.fractions e (some i)

/-- The full tree of public receipts, in the order the child calls were made.
The type records the actual depth of every child. -/
inductive Receipt (N ne r : ℕ) : ℕ → Type
  | leaf (l : ℕ) : Receipt N ne r l
  | node (l : ℕ) (events : Fin (2*r) → RoundData N ne l)
      (subruns : Fin (2*r) → Receipt N ne r (l + 1)) : Receipt N ne r l

structure Output (N ne r l : ℕ) where
  prices : Prices N l
  trace : Trial (Fin ne) r
  receipt : Receipt N ne r l
  /-- The execution reads these cached integers when the child returns. -/
  scores : Vector ℕ ne
  scores_eq : ∀ e : Fin ne, scores[e] = trace.score scaleQ sigmaQ e
  log : List (Probe N)

abbrev Certified {N ne r l : ℕ} (w : Weights ne) :=
  {o : Output N ne r l // o.trace.Admissible scaleQ sigmaQ eta (fun e => (w e : ℝ))}

structure Call (N ne r l : ℕ) where
  data : RoundData N ne l
  child : Output N ne r (l + 1)

/-- The probe/child tables read only cached gains and integer scores. -/
def callGain {N ne r l : ℕ} (c : Call N ne r l) (e : Fin ne) : ℚ := c.data.gain[e]

def callScore {N ne r l : ℕ} (c : Call N ne r l) (e : Fin ne) : ℕ := c.child.scores[e]

def incomingLocal {N ne r l j : ℕ} (experts : Fin ne → Expert N) (w : Weights ne)
    (xs : Fin j → Call N ne r l) : Weights ne :=
  localWeightQ etaQ (localPartQ (mask experts l) w) (probeAt fun t => callGain (xs t)) j

def incomingDeep {N ne r l j : ℕ} (experts : Fin ne → Expert N) (w : Weights ne)
    (xs : Fin j → Call N ne r l) : Weights ne :=
  deepWeightQ (deepPartQ (mask experts l) w) (probeAt fun t => callScore (xs t)) j

/-- The certificate relates one returned child to the earlier, immutable prefix.
The first group also records primal market balance and the exact feedback gain. -/
structure StepOK {N ne r l j : ℕ} (experts : Fin ne → Expert N) (w : Weights ne)
    (xs : Fin j → Call N ne r l) (c : Call N ne r l) : Prop where
  admissible : c.child.trace.Admissible scaleQ sigmaQ eta (fun e => (incomingDeep experts w xs e : ℝ))
  nonneg : ∀ e i, 0 ≤ c.data.alloc e i
  mass : ∀ e, ∑ i, c.data.alloc e i ≤ 1
  gain_eq : ∀ e, c.data.gain[e] = gainQ c.data.alloc (sides experts) (fun i => labelSign (c.data.labels i)) e
  probeMarket : j < r → ∃ S, c.data.market = some S ∧ S.experts = experts ∧
    S.weights = incomingLocal experts w xs
  finalMarket : r ≤ j → c.data.market = none
  clears : j < r → ∀ i, ∑ e, incomingLocal experts w xs e * sides experts e * c.data.alloc e i = 0

end TrialExecution
end PriceGame
end LinearProgramming
end Optimization
end OAI

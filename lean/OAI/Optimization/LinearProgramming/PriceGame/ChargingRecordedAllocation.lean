import OAI.Optimization.LinearProgramming.PriceGame.ChargingExpertsAllocation
import OAI.Optimization.LinearProgramming.PriceGame.TrialExecutionAssembleFacts
import OAI.Optimization.LinearProgramming.PriceGame.StatesReachable
import OAI.Optimization.LinearProgramming.PriceGame.ChargingSkeleton

/-! # Charging the exact gain carried by a completed probe event -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Charging

open Finset States.Mass TrialExecution

variable {V : Type} [Fintype V] [DecidableEq V] {N ne l : ℕ}

/-- Repackage the recorded market's maximizing answer using the original expert roster
and the actual baseline of the event. -/
abbrev recordedMarket {experts : Fin ne → Expert N} {L : Weights ne}
    {event : RoundData N ne l} {snap : MarketSnapshot N ne l} (rec : RecordedProbe experts L event snap) :
    MarketAnswer experts l snap.history L :=
  ⟨event.baseline, snap.answer.fractions, rec.balanced⟩

/-- Run the two probe tests using the actual receipt (including the outside fraction),
the observed comparison table and a reachable feedback vector. On a passing test,
the bound concerns exactly the recorded gain of the selected roster row. On a failed
test, `failed_actual_child` recovers failure in each supported state. -/
theorem recorded_probe_test {R : ℕ} {anchor : Fin N} (hidden : Hidden N R anchor)
    {k : Fin (depth N)} {experts : Fin ne → Expert N} {L : Weights ne}
    {event : RoundData N ne k} {snap : MarketSnapshot N ne k} (rec : RecordedProbe experts L event snap)
    (v : V ↪ Vertex N k) (select : (Fin 64 → V) → Fin ne) (m : V → ℚ)
    (pivot : Pivot N k) (truth : Fin N → ℚ)
    (hsk : ∀ x, (experts (select x)).skeleton = tupleSkeleton k hidden.positive (fun j => v (x j)) pivot)
    (keeps : ∀ x, ∀ t ∈ (tupleSkeleton k hidden.positive (fun j => v (x j)) pivot).testsAt
        ⟨k,event.baseline,snap.history⟩,
        compare (featureValue (experts (select x)).raw t.feature) t.threshold =
        compare (featureValue truth t.feature) t.threshold)
    {S : Vertex N k → Prop} (live : ∀ j, S (v j)) (path : States.Path (Fin N) (Vertex N k))
    (reached : States.Reachable hidden.positive (States.priority hidden) (· ∈ hidden.active) path
      (fun i => truth (rootVertex N k i)) S (historyShift hidden.positive pivot truth snap.history))
    (runs : Computation.Reaches hidden (States.feedbackAll path event.baseline event.childPrices) event.labels)
    (hm : ∀ j, 0 ≤ m j) (hM0 : 0 < ∑ j, m j) (hM1 : ∑ j, m j ≤ 1) :
    let P := fun i => truth (rootVertex N k i)
    let t := historyShift hidden.positive pivot truth snap.history
    Nonempty (ProbeTest m (fun j => probeSurplus P event.baseline hidden.positive t (v j))
      (actualSuccess v S P event.baseline hidden.positive t event.childPrices)
      (weighted (tupleDistribution m) (fun tuple => event.gain[select tuple]))) := by
  let P := fun i => truth (rootVertex N k i)
  let h := hidden.positive
  let t := historyShift h pivot truth snap.history
  let surplus (i : V) := probeSurplus P event.baseline h t (v i)
  let label (i : V) := labelAgreement h (event.labels (v i))
  let A : ProbeAllocation 64 surplus := selectedMarketAllocation (k := k) (recordedMarket rec)
    v select h pivot truth hsk keeps
  let success := actualSuccess v S P event.baseline h t event.childPrices
  have correct (u : ℚ) (hu : t ≤ u) (pass : childPass S P event.baseline h u event.childPrices)
      (i : V) (hm : States.signed h (event.baseline (v i)) ≤ P (v i) - u) :
      label i = 1 := by
    have good := States.feedbackAll_correct hidden reached hu event.childPrices pass event.labels runs
      (v i) (live i) hm
    exact (show labelAgreement hidden.positive (event.labels (v i)) = 1 by simp [labelAgreement, good])
  have inherit : success none → ∀ i, 0 ≤ surplus i → label i = 1 := by
    intro win i hi
    exact correct t le_rfl win.2 i (sub_nonneg.mp hi)
  have pivots : ∀ j, success (some j) → ∀ i, surplus j ≤ surplus i → label i = 1 := by
    intro j win i hi
    apply correct _ win.1 win.2 i
    change States.signed h (event.baseline (v i)) ≤ P (v i) - (P (v j) - States.signed h (event.baseline (v j)))
    change P (v j) - t - States.signed h (event.baseline (v j)) ≤
      P (v i) - t - States.signed h (event.baseline (v i)) at hi
    linarith
  have test := exists_probe_test m surplus label A hm hM0 hM1 (fun _ => labelAgreement_lower _ _) success inherit pivots
  have actualGain : probeGain A label = fun x => event.gain[select x] := by
    funext x
    have eq := selectedMarket_gain (k := k) (recordedMarket rec) v select h pivot truth hsk keeps event.labels x
    refine eq.trans ?_
    simpa only [rec.alloc_eq] using (rec.gain_eq (select x)).symm
  exact (congrArg (fun f => Nonempty (ProbeTest m surplus success (weighted (tupleDistribution m) f))) actualGain).mp test

/-- The local-score input to the failed-node induction, specialized to the actual
finite state, roster selector, and event gain. The active type is the subtype of the
state's active set. All original tuple positions are retained when selecting a row. -/
theorem recorded_state_allocation {R : ℕ} {anchor : Fin N} (hidden : Hidden N R anchor)
    (s : States.FiniteState N l) (hlt : l < depth N) (sel : Skeleton N → Fin ne)
    {experts : Fin ne → Expert N} {L : Weights ne}
    {event : RoundData N ne l} {snap : MarketSnapshot N ne l} (rec : RecordedProbe experts L event snap)
    (hist : History N) (hsnap : snap.history = hist)
    (hsk : ∀ sk : Skeleton N, sk.positive = hidden.positive → (experts (sel sk)).skeleton = sk)
    (keeps : ∀ sk : Skeleton N, sk.positive = hidden.positive → ∀ test ∈ sk.testsAt ⟨l,event.baseline,hist⟩,
      compare (featureValue (experts (sel sk)).raw test.feature) test.threshold =
      compare (featureValue (States.priority hidden) test.feature) test.threshold) :
    ∃ A : ProbeAllocation 64 (fun i : s.active => s.surplus hidden hist event.baseline i),
      ∀ x : Fin 64 → s.active,
        probeGain A (fun i => if event.labels i = hidden.positive then 1 else -1) x =
        event.gain[sel (localSkeleton hidden.positive s.pivot hlt (fun j => x j))] := by
  subst hist
  let k : Fin (depth N) := ⟨l,hlt⟩
  let v : s.active ↪ Vertex N l := Function.Embedding.subtype _
  let sk (x : Fin 64 → s.active) := localSkeleton hidden.positive s.pivot hlt (fun j => x j)
  let choose (x : Fin 64 → s.active) := sel (sk x)
  have hlo (x) : (experts (choose x)).skeleton = tupleSkeleton k hidden.positive (fun j => v (x j)) s.pivot :=
    hsk (sk x) rfl
  have agree (x) : ∀ test ∈ (tupleSkeleton k hidden.positive (fun j => v (x j)) s.pivot).testsAt
        ⟨k,(recordedMarket rec).prices,snap.history⟩,
      compare (featureValue (experts (choose x)).raw test.feature) test.threshold =
      compare (featureValue (States.priority hidden) test.feature) test.threshold := keeps (sk x) rfl
  let raw (i : s.active) := probeSurplus (fun j => States.priority hidden (rootVertex N k j))
    event.baseline hidden.positive (historyShift hidden.positive s.pivot (States.priority hidden) snap.history) i
  have eq : raw = fun i : s.active => s.surplus hidden snap.history event.baseline i := by
    funext i
    have hs : historyShift hidden.positive s.pivot (States.priority hidden) snap.history =
        s.shift hidden snap.history := by
      unfold States.FiniteState.shift
      cases s.pivot <;> rfl
    simp only [raw, probeSurplus, hs, States.FiniteState.surplus, States.FiniteState.value, k]
  have result : ∃ A : ProbeAllocation 64 raw, ∀ x : Fin 64 → s.active,
      probeGain A (fun i => if event.labels i = hidden.positive then 1 else -1) x =
      event.gain[choose x] := by
    refine ⟨selectedMarketAllocation (k := k) (recordedMarket rec) v choose hidden.positive s.pivot
      (States.priority hidden) hlo agree, ?_⟩
    intro x
    have hgain := selectedMarket_gain (k := k) (recordedMarket rec) v choose hidden.positive s.pivot
      (States.priority hidden) hlo agree event.labels x
    refine hgain.trans ?_
    simpa only [rec.alloc_eq] using (rec.gain_eq (choose x)).symm
  rwa [eq] at result

end Charging
end PriceGame
end LinearProgramming
end Optimization
end OAI

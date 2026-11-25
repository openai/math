import OAI.Optimization.LinearProgramming.PriceGame.ChargingDeep
import OAI.Optimization.LinearProgramming.PriceGame.ChargingSkeleton

/-! # The failed-node induction step on an actual finite price-game state -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Charging

open Finset States States.Mass

/-- Every final call uses the same coordinatewise median of the first group. -/
def callBaseline {k : ℕ} {I : Type*} (probe : Calls k → I → ℚ) : Sum (Calls k) (Calls k) → I → ℚ :=
  Sum.elim probe (fun _ i => oddMedian fun b => probe b i)

/-- The exact source threshold from `d₀=64` and `δ=1/16`. -/
def chargeSigma : ℚ := (1/16 : ℚ) / (32*(8/(1/16 : ℚ)^65))

/-- Section 6.2 at a nonleaf. The induction hypothesis is required only for
actual possible successors whose shared child prices fail. The indicated local
and deeper score formulas identify the integers returned by the public trial.
For the probes, both the maximizing allocation and the designated oracle replies
are those at that call's baseline. -/
theorem charge_state_node {N R l fuel k : ℕ} {anchor : Fin N} {E : Type*} [DecidableEq E] [Fintype E]
    {h : Hidden N R anchor} {history : History N} {path : Path (Fin N) (Vertex N l)}
    {s : FiniteState N l} (p : Possible h history path s) (bound : l+(fuel+1) ≤ depth N)
    (sel : Skeleton N → E) (probe : Calls k → Vertex N l → ℚ)
    (childPrices : Sum (Calls k) (Calls k) → Vertex N (l+1) → ℚ)
    (labels : Calls k → Vertex N l → Bool)
    (reads : ∀ b, Computation.Reaches h (feedbackAll path (probe b) (childPrices (.inl b))) (labels b))
    (alloc : ∀ b, ProbeAllocation 64 (fun i : s.active => s.surplus h history (probe b) i))
    (parentScore : E → ℚ) (childScore : Sum (Calls k) (Calls k) → E → ℚ)
    (hchildNonneg : ∀ b e, 0 ≤ childScore b e)
    (localScore : ∀ x : Fin 64 → s.active,
      parentScore (sel (localSkeleton h.positive s.pivot (by omega : l < depth N) (fun j => x j))) =
        (roundCharge chargeSigma (weighted (uniform k) (fun b => probeGain (alloc b)
          (fun i => if labels b i = h.positive then 1 else -1) x)) : ℚ))
    (deepScore : ∀ a : DeeperSkeleton (Vertex N l) 64 fuel,
      let id := sel (absoluteSkeleton h.positive s.pivot bound ⟨a.1.succ,a.2.1,a.2.2⟩)
      parentScore id = (roundCharge chargeSigma
        (weighted (childWeights (uniform k)) (fun b => childScore b id)) : ℚ))
    (childIH : ∀ b (o : Option (Vertex N l)),
      let y := callBaseline probe b
      let next := s.child h history y o
      Possible h (k := l+1) (history.push l y) (.extend path y (vertexDecidableEq N l)) next →
      ¬next.wins h (history.push l y) (childPrices b) →
      1 ≤ weighted (stateWeight h next (by omega : l+1+fuel ≤ depth N) sel) (childScore b))
    (failure : ¬s.wins h history (fun i => oddMedian (fun b =>
      parentPrices (callBaseline probe (.inr b)) (childPrices (.inr b)) i))) :
    1 ≤ weighted (stateWeight h s bound sel) parentScore := by
  classical
  let m := weight N l h.positive
  let activeMass := fun i : s.active => m i
  let y := callBaseline probe
  let q := fun b => s.surplus h history (y b)
  let c := fun b => stateScores h s bound sel (childScore b)
  let w := deeperWeight (arity := 64) (levels := fuel) (s.ambientMass h)
  let wc := fun b (o : Option s.active) => childDeeperWeight (arity := 64) (levels := fuel)
    ((s.child h history (y b) (o.map Subtype.val)).ambientMass h) (o.map Subtype.val)
  have hm (i) : 0 ≤ m i := weight_nonneg N l h.positive i
  have hm0 : 0 < ∑ i, activeMass i := (s.sum_on_active h).trans_gt p.mass_pos
  have hm1 : ∑ i, activeMass i ≤ 1 := (s.sum_on_active h).trans_le p.mass_le
  have hmambient : ∑ i, s.ambientMass h i ≤ 1 := (sum_maskedMass s.active m).trans_le p.mass_le
  have hwm (i) : 0 ≤ s.ambientMass h i := maskedMass_nonneg s.active m hm i
  have hresult := trial_charge_of_child_states (F := DeeperSkeleton (Vertex N l) 64 fuel) h.positive activeMass
    (fun i : s.active => s.priceThreshold h history i) (fun b i => probe b i)
    (fun b i => parentPrices (y (.inr b)) (childPrices (.inr b)) i)
    (fun b i => q b i) (fun b i => if labels b i = h.positive then 1 else -1) alloc
    (fun b => s.testPass h history (y b) (childPrices b)) w wc (fun b => deeperScores (c b))
    (fun i => hm i) hm1 hm0 (deeperWeight_nonneg _ hwm) (sum_deeperWeight_le_one _ hwm hmambient 64 fuel)
    (fun b e => hchildNonneg b _) (fun b i => by split <;> norm_num)
    (fun b => s.positiveMass_eq_violatedMass h history (probe b))
    (fun b => s.positiveMass_eq_violatedMass h history (y (.inr b)))
    (fun b => p.probeTest_of_feedbackAll (probe b) (childPrices (.inl b)) (labels b) (reads b) (alloc b))
    ((s.fails_iff_exists_miss h history _).mp failure)
    (fun b hb i => s.inherited_pass_mapped h history (y (.inr b)) (childPrices (.inr b)) hb i) ?_ ?_
  · change 1 ≤ ∑ e, stateWeight h s bound sel e * parentScore e
    rw [stateWeight_scores]
    change 1 ≤ scoreMass (maskedMass s.active m) (stateScores h s bound sel parentScore)
    rw [scoreMass_split_sums s.active m hm]
    apply hresult.trans_eq
    apply congrArg₂ (· + ·)
    · apply sum_congr rfl; intro x _
      have heq := absoluteSkeleton_local (levels := fuel) h.positive s.pivot bound
        (localTuple (fun j : Fin 64 => (x j : Vertex N l)))
      exact congrArg (fun z : ℚ => (∑ i, activeMass i)^64/4 * tupleDistribution activeMass x * z)
        ((localScore x).symm.trans (congrArg (fun a => parentScore (sel a)) heq.symm))
    · apply sum_congr rfl; intro a _
      exact congrArg (fun z : ℚ => w a * z) (deepScore a).symm
  · intro b μ hμ hμsum hcap _ e
    have hcmp := deepChildWeight_transfer h.positive s.active m hm
      (fun o => s.strictSet h history (y b) (o.map Subtype.val)) (fun o => s.strictSet_subset ..)
      μ hμ hμsum hcap e
    simp only [wc, FiniteState.child_ambientMass]
    rw [show (8 : ℚ)/(1/16 : ℚ)^65 = 8*16^(64+1) by norm_num]
    exact hcmp
  · intro b o hadm hfail
    obtain ⟨pnext,hn⟩ := p.failed_child (by omega : l < depth N) (y b) (childPrices b) o hadm hfail
    have ih := childIH b (o.map Subtype.val) pnext hn
    change 1 ≤ ∑ e, stateWeight _ _ _ _ e * childScore b e at ih
    rw [stateWeight_scores] at ih
    have eq := sum_childDeeperWeight_scores ((s.child h history (y b) (o.map Subtype.val)).ambientMass h)
      (o.map Subtype.val) (c b)
    rw [show childScores (o.map Subtype.val) (c b) = _ from child_stateScores h s bound sel (childScore b)
      history (y b) (o.map Subtype.val)] at eq
    exact ih.trans_eq eq.symm

end Charging
end PriceGame
end LinearProgramming
end Optimization
end OAI

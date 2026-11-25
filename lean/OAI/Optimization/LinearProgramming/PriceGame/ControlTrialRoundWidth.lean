import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialSourceWire
import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialSourceGuarded
import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialEnvelope
import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialCost
import OAI.Optimization.LinearProgramming.PriceGame.ControlCampaignArrayBounds
import OAI.Optimization.LinearProgramming.PriceGame.ControlCampaignNative
import OAI.Optimization.LinearProgramming.PriceGame.ControlEncodingGuard

/-! Numerical bit bounds on every intermediate first-order trial instruction reached
from the actual evolving campaign catalogue, including both branches of every query. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Wire

open Campaign Learning States.Mass TrialExecution Trial Moment

attribute [local irreducible] Moment.probes TrialExecution.run TrialExecution.execute

private theorem gain_bound (b w : ℕ) (cap : 2*(3+4*b)+4 ≤ w) :
    2*(3+2*(b+b))+4 ≤ w := by omega

private theorem local_grid_positive (Q r : ℕ) (hQ : 0 < Q) : 0 < Q*etaQ.den^r :=
  Nat.mul_pos hQ (Nat.pow_pos etaQ.den_pos)

private theorem root_good_of_arrays {N ne : ℕ} (env : Envelope) (r R D Q L B k : ℕ)
    (es : Fin ne → Expert N) (w : Weights ne) (hw : ∀ e, 0 ≤ w e) (hk : k ≤ depth N)
    (fits : env.TrialArraysFit r R es k 0 .root (fun _ _ => 0) w hw)
    (registers : WeightRegistersWithin r R es Q L B k 0 .root (fun _ _ => 0) w hw) :
    Source.NodeGood env r R D Q L B es k (SourceNode.initial N w hw) where
  level := (Nat.zero_add k).le.trans hk
  path := True.intro
  prior := fun j hj => (Nat.not_lt_zero j hj).elim
  arrays := ⟨fits,registers⟩

private theorem history_root_marks {N : ℕ} (a : Fin N) (R T : ℕ)
    (hT : T ≤ (N+R.size+1)^300) (old : ℕ → RoundResult N) (t : ℕ) (ht : t ≤ T)
    (sized : ∀ j < t, PublicRoundBounds (population R old j) (old j)) :
    let p := population R old t
    let Q := populationDenominator R old t
    let L := Q*etaQ.den^probes
    let B := registerWeightPolynomial.eval (N+R.size+1)
    let env := campaignEnvelope N R T
    Source.Limits env probes R Bits.commonDenominator L B B (populationExperts p) ∧
      Source.NodeGood env probes R Bits.commonDenominator Q L B (populationExperts p) (depth N)
        (SourceNode.initial N (populationWeights p) p.nonnegative) := by
  let p := population R old t
  let Q := populationDenominator R old t
  let L := Q*etaQ.den^probes
  let B := registerWeightPolynomial.eval (N+R.size+1)
  let env := campaignEnvelope N R T
  have hs j hj := (sized j hj).observations
  have count : p.experts.length ≤ expertCount N R T := population_length_at_prefix a R T old t ht hs
  have raw : RawBox Bits.commonDenominator R (populationExperts p) := by
    intro e i _
    apply Pool.catalogue_entry_grid (hist := seenProbes old) (T := t+1)
    rw [← population_entries]
    exact List.getElem_mem ..
  have price : 2*trialPriceBits N (expertCount N R T) R Bits.commonDenominator+4 ≤ env.width :=
    Nat.le_add_right _ _
  have gain : 2*(3+4*B)+4 ≤ env.width := Nat.le_add_left _ _
  have hlim : Source.Limits env probes R Bits.commonDenominator L B B (populationExperts p) := {
    nonempty := a.pos
    den := Bits.commonDenominator_pos
    localDen := local_grid_positive Q probes (populationDenominator_pos a R old t)
    localBits := actual_localGrid_bound a R T hT old t ht hs
    raw := raw
    depth := le_rfl
    vertices := le_rfl
    experts := count
    price := (Nat.add_le_add_right (Nat.mul_le_mul_left 2
      (trialPriceBits_mono_experts N R Bits.commonDenominator count)) 4).trans price
    gain := gain_bound B _ gain
    score := le_rfl
    log := envelope_log_limit N R T }
  exact ⟨hlim, root_good_of_arrays env probes R Bits.commonDenominator Q L B (depth N)
    (populationExperts p) (populationWeights p) p.nonnegative le_rfl
    (prefix_trial_array_bounds env a R T hT le_rfl le_rfl le_rfl price gain old t ht sized)
    (prefix_weight_registers_polynomial a R T hT old t ht sized)⟩

/-- The real native round, started at any public prefix with its own observed population.
Its certified length is uniform on every internal program counter, including the final return. -/
theorem run_round_guarded_width {N : ℕ} (a : Fin N) (R T : ℕ) (hT : T ≤ (N+R.size+1)^300)
    (old : ℕ → RoundResult N) (t : ℕ) (ht : t ≤ T)
    (sized : ∀ j < t, PublicRoundBounds (population R old j) (old j)) (positive : ℕ)
    {tr round} (actual : Emits (runRound R (Driver.commonMarkets N) (population R old t)) tr round) :
    let p := population R old t
    let c := Driver.sourceCursor R T (T-t) a p positive
    ∃ stop, GuardedSteps (fun s => (stateCode s).length ≤
        (campaignEnvelope N R T).stateSize (2*probes) (totalTrialTicks N))
      (Driver.kernel c) (2*probes) (initial (depth N) (Driver.rootInput c)) tr
      (nodeTicks (2*probes) (depth N)+tr.length) stop ∧
      step (Driver.kernel c) (2*probes) stop = .halt (packRound p.experts.length round) := by
  let p := population R old t
  let env := campaignEnvelope N R T
  let c := Driver.sourceCursor R T (T-t) a p positive
  let es := populationExperts p
  let w := populationWeights p
  let solve := marketSolverAtCommonWeightUnit es
  change Emits ((TrialExecution.run R es solve w p.nonnegative).map (resultOf p)) tr round at actual
  obtain ⟨receipt,source,rfl⟩ := actual.map_inv
  obtain ⟨hlim,hroot⟩ := history_root_marks a R T hT old t ht sized
  let marks := Source.sourceMarks hlim (populationDenominator R old t)
  obtain ⟨stop,proof,halt⟩ := marks.rootGuarded w p.nonnegative hroot source
  have ticks : nodeTicks (2*probes) (depth N)+tr.length ≤ totalTrialTicks N := by
    have same : probes = Complexity.probes := by unfold Moment.probes Complexity.probes; rfl
    rw [same]
    exact trial_ticks_polynomial a.pos R es solve w p.nonnegative source
  have small := env.guarded_state_length proof ticks
  have eqKernel : Driver.kernel c =
      packetKernel feedbackPrefix N R probes (List.ofFn fun i => packExpert (es i)) :=
    congrArg (packetKernel feedbackPrefix N R probes) (Driver.packed_roster p).symm
  have eqInput : Driver.rootInput c = codeInput (N:=N) 0 (fun _ _ => 0) w :=
    Driver.code_rootInput R T (T-t) a p positive
  dsimp only
  change ∃ last, GuardedSteps _ (Driver.kernel c) _ (initial _ (Driver.rootInput c)) _ _ last ∧
    step (Driver.kernel c) _ last = .halt (packRound p.experts.length (resultOf p receipt))
  rw [eqKernel,eqInput,← Driver.packed_resultOf p receipt]
  exact ⟨stop,small,halt⟩

end Wire
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI

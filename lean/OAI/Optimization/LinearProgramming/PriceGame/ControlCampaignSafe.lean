import OAI.Optimization.LinearProgramming.PriceGame.ControlCampaignTrace
import OAI.Optimization.LinearProgramming.PriceGame.ControlCampaignCommon
import OAI.Optimization.LinearProgramming.PriceGame.ControlCampaignScoreGuard

/-! # Numeric guards on every genuine campaign execution -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Driver

set_option exponentiation.threshold 274 in
theorem outerGuardedRoundCompiler (N R : ℕ) :
    GuardedRoundCompiler N R (fun s => OuterSafe s ∧ DimensionAt N s) := by
  intro T n a p positive tr round run
  let c := sourceCursor R T (n+1) a p positive
  let out := packRound p.experts.length round
  have ev : Trial.Evaluates (kernel c) (2*Moment.probes) (.node (States.Mass.depth c.dimension)
      (rootInput c)) tr out := by
    rw [show rootInput c = Trial.codeInput 0 (N:=N) (fun _ _ => 0) (Campaign.populationWeights p) from
      code_rootInput R T (n+1) a p positive]
    exact commonRoundCompilation N R p tr round run
  have hs : ∀ i < c.state.population.weights.length, out.scores[i]?.getD 0 ≤ (2*c.dimension)^274 :=
    Trial.runRound_scoreGuard R (commonMarkets N) p (Nat.zero_lt_of_lt a.isLt) run
  have first := guarded_one_round (N := N) (c := c) (Nat.zero_lt_succ n) rfl hs ev
  have eq : finishRound c out = _ := finish_sourceCursor R T n a p positive round
  rwa [eq] at first

/-- The public dimension stays fixed. At each instruction consuming a root output,
all materialized score powers are bounded by the uniform cap polynomial. -/
theorem campaign_safe_steps {N R T : ℕ} (a : Fin N) {tr bit}
    (hr : Trial.Emits (Computation.ofTree (Campaign.strategy R T a (commonMarkets N))) tr bit) :
    ∃ last, GuardedSteps (fun s => OuterSafe s ∧ DimensionAt N s)
        (.campaign (startCampaign N R a.val T)) tr
        (T * (Trial.nodeTicks (2*Moment.probes) (States.Mass.depth N) + 2) + tr.length) (.campaign last) ∧
      step (.campaign last) = .halt bit ∧ DimensionAt N (.campaign last) :=
  campaign_guarded_steps (outerGuardedRoundCompiler N R) a hr

end Driver
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI

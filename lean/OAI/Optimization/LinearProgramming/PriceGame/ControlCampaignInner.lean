import OAI.Optimization.LinearProgramming.PriceGame.ControlCampaignInnerRoot
import OAI.Optimization.LinearProgramming.PriceGame.ControlCampaignTrace
import OAI.Optimization.LinearProgramming.PriceGame.ControlCampaignGuardIntersection
import OAI.Optimization.LinearProgramming.PriceGame.ControlCampaignSafe
import OAI.Optimization.LinearProgramming.PriceGame.ControlCampaignTrialMarks

/-! # Lifting verified per-trial kernel conditions to the whole adaptive controller -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Driver

theorem inner_guarded_compiler {N R : ℕ} {P : InnerPredicate} (inner : InnerRoundCompiler N R P) :
    GuardedRoundCompiler N R (InnerHolds P) := by
  intro T n a p positive tr round e
  let c := sourceCursor R T (n+1) a p positive
  let out := packRound p.experts.length round
  obtain ⟨last,inside,done⟩ := inner p e
  have path : Trial.GuardedSteps (P c.dimension c.range c.state.population.experts) (kernel c) (2*Moment.probes)
      (Trial.initial (States.Mass.depth c.dimension) (rootInput c)) tr
      (Trial.nodeTicks (2*Moment.probes) (States.Mass.depth c.dimension)+tr.length) last := by
    rw [show rootInput c = Trial.codeInput 0 (N:=N) (fun _ _ => 0) (Campaign.populationWeights p) from
      code_rootInput R T (n+1) a p positive]
    exact inside
  have d : Trial.step (kernel c) (2*Moment.probes) last = .halt out := done
  have full := guarded_round_of_marked_root (P := InnerHolds P) (c := c)
    (Nat.zero_lt_succ n) trivial path d
  have eq : finishRound c out = _ := finish_sourceCursor R T n a p positive round
  rwa [eq] at full

theorem full_guarded_compiler {N R : ℕ} {P : InnerPredicate} (inner : InnerRoundCompiler N R P) :
    GuardedRoundCompiler N R (fun s => (OuterSafe s ∧ DimensionAt N s) ∧ InnerHolds P s) := by
  intro T n a p positive tr round e
  exact (outerGuardedRoundCompiler N R T n a p positive e).zip
    (inner_guarded_compiler inner T n a p positive e)

end Driver
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI

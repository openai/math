import OAI.Optimization.LinearProgramming.PriceGame.ControlCampaignInnerType
import OAI.Optimization.LinearProgramming.PriceGame.ControlCampaignNative
import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialGuarded

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Driver

/-- The reusable single-root contract records all intermediate stack guards as well
as the actual chronological query transcript and the exact returned packet. -/
def InnerRoundCompiler (N R : ℕ) (P : InnerPredicate) : Prop :=
  ∀ (p : Population N) {tr round}, Trial.Emits (Campaign.runRound R (commonMarkets N) p) tr round →
    let ops := Trial.packetKernel feedbackPrefix N R Moment.probes (packPopulation p).experts
    ∃ last, Trial.GuardedSteps (P N R (packPopulation p).experts) ops (2*Moment.probes)
        (Trial.initial (States.Mass.depth N) (Trial.codeInput 0 (N:=N) (fun _ _ => 0)
          (Campaign.populationWeights p))) tr
        (Trial.nodeTicks (2*Moment.probes) (States.Mass.depth N)+tr.length) last ∧
      Trial.step ops (2*Moment.probes) last = .halt (packRound p.experts.length round)

/-- Lift a guarded run of the root compiler through the actual summary map. Both
the packed expert order and the returned score order are preserved. -/
theorem innerRoundCompiler_of_root {N R : ℕ} {P : InnerPredicate}
    (source : ∀ {ne : ℕ} (experts : Fin ne → Expert N)
      (w : TrialExecution.Weights ne) (hw : ∀ e, 0 ≤ w e) {tr out},
      Trial.Emits (TrialExecution.run R experts (TrialExecution.marketSolverAtCommonWeightUnit experts) w hw) tr out →
      let roster := List.ofFn (fun e => packExpert (experts e))
      let ops := Trial.packetKernel feedbackPrefix N R Moment.probes roster
      ∃ last, Trial.GuardedSteps (P N R roster) ops (2*Moment.probes)
          (Trial.initial (States.Mass.depth N) (Trial.codeInput 0 (N:=N) (fun _ _ => 0) w)) tr
          (Trial.nodeTicks (2*Moment.probes) (States.Mass.depth N)+tr.length) last ∧
        Trial.step ops (2*Moment.probes) last = .halt (Trial.codeOutput out.val)) :
    InnerRoundCompiler N R P := by
  intro p tr round e
  obtain ⟨receipt,actual,rfl⟩ := e.map_inv
  have ref := source (Campaign.populationExperts p) (Campaign.populationWeights p) p.nonnegative actual
  dsimp only at ref ⊢
  rwa [packed_roster,packed_resultOf] at ref

end Driver
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI

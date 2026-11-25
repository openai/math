import OAI.Optimization.LinearProgramming.PriceGame.ControlCampaignNative
import OAI.Optimization.LinearProgramming.PriceGame.ControlCampaignGuarded

/-! # Composing genuine round guards along a complete campaign trace -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Driver

/-- One guarded physical run between two consecutive outer states, uniformly over
the current roster, vote count, remaining trials and returned observations. -/
def GuardedRoundCompiler (N R : ℕ) (P : PC → Prop) : Prop :=
  ∀ (T n : ℕ) (a : Fin N) (p : Population N) (positive : ℕ) {tr round},
    Trial.Emits (Campaign.runRound R (commonMarkets N) p) tr round →
    GuardedSteps P (.campaign (sourceCursor R T (n+1) a p positive)) tr
      (Trial.nodeTicks (2*Moment.probes) (States.Mass.depth N) + tr.length + 2)
      (.campaign (sourceCursor R T n a (p.advance (Learning.Pool.batch N R) round) (positive + vote a round)))

private theorem warm_guarded {N R : ℕ} {P : PC → Prop} (compiled : GuardedRoundCompiler N R P)
    (T : ℕ) (a : Fin N) (left : ℕ) (p : Population N) (positive : ℕ) {tr bit}
    (hr : Trial.Emits (stream (Learning.Pool.batch N R) (Campaign.runRound R (commonMarkets N)) a T left p positive) tr bit) :
    ∃ last, GuardedSteps P (.campaign (sourceCursor R T left a p positive)) tr
        (left * (Trial.nodeTicks (2*Moment.probes) (States.Mass.depth N) + 2) + tr.length) (.campaign last) ∧
      step (.campaign last) = .halt bit ∧ DimensionAt N (.campaign last) := by
  induction left generalizing p positive tr bit with
  | zero =>
    cases hr
    refine ⟨sourceCursor R T 0 a p positive,?_,?_,rfl⟩
    · simpa using GuardedSteps.refl (P := P) (.campaign (sourceCursor R T 0 a p positive))
    · simp [sourceCursor,step,campaignBoundary,stateOf]
      rfl
  | succ n ih =>
    rw [stream] at hr
    obtain ⟨before,round,after,rfl,hBefore,hAfter⟩ := hr.bind_inv
    obtain ⟨last,later,done,dimLast⟩ := ih _ _ hAfter
    have all := (compiled T n a p positive hBefore).trans later
    refine ⟨last,?_,done,dimLast⟩
    convert all using 1
    simp only [List.length_append,Nat.succ_mul]
    omega

/-- Per-round guards imply the same predicate at every executed campaign instruction,
with the exact deterministic silent-instruction and query count. -/
theorem campaign_guarded_steps {N R T : ℕ} {P : PC → Prop} (compiled : GuardedRoundCompiler N R P)
    (a : Fin N) {tr bit}
    (hr : Trial.Emits (Computation.ofTree (Campaign.strategy R T a (commonMarkets N))) tr bit) :
    ∃ last, GuardedSteps P (.campaign (startCampaign N R a.val T)) tr
        (T * (Trial.nodeTicks (2*Moment.probes) (States.Mass.depth N) + 2) + tr.length) (.campaign last) ∧
      step (.campaign last) = .halt bit ∧ DimensionAt N (.campaign last) := by
  rw [← stream_eq_strategy,ofTree_toTree] at hr
  obtain ⟨last,valid,done,dim⟩ := warm_guarded compiled T a _ _ _ hr
  have initial : startCampaign N R a.val T = sourceCursor R T T a (.start (Learning.Pool.batch N R)) 0 :=
    congrArg (fun s => CampaignCursor.mk N R a.val T T s) (startCampaign_state N R a.val T)
  exact ⟨last,initial ▸ valid,done,dim⟩

end Driver
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI

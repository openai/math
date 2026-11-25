import OAI.Optimization.LinearProgramming.PriceGame.ControlCampaignNative
import OAI.Optimization.LinearProgramming.PriceGame.ControlCampaignTrialMarks
import OAI.Optimization.LinearProgramming.PriceGame.ControlCampaignGuardIntersection

/-! # History-indexed invariants for a whole adaptive finite-state campaign -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Driver

/-- The source-prefix invariant may depend on the elapsed trial count, entire typed
population and accumulated votes. The inner trial and outer cursor use the same
public predicate on full first-order states. -/
structure CampaignMarks {N : ℕ} (R T : ℕ) (a : Fin N) (P : PC → Prop) where
  HistoryGood : ℕ → Population N → ℕ → Prop
  initial : HistoryGood 0 (.start (Learning.Pool.batch N R)) 0
  advance (t : ℕ) (ht : t<T) (p : Population N) (positive : ℕ) (good : HistoryGood t p positive)
      {tr round} (e : Trial.Emits (Campaign.runRound R (commonMarkets N) p) tr round) :
      HistoryGood (t+1) (p.advance (Learning.Pool.batch N R) round) (positive+vote a round)
  outer (t : ℕ) (ht : t≤T) (p : Population N) (positive : ℕ) (good : HistoryGood t p positive) :
      P (.campaign (sourceCursor R T (T-t) a p positive))
  inner (t : ℕ) (ht : t<T) (p : Population N) (positive : ℕ) (good : HistoryGood t p positive)
      {tr round} (e : Trial.Emits (Campaign.runRound R (commonMarkets N) p) tr round) :
      let c := sourceCursor R T (T-t) a p positive
      ∃ stop, Trial.GuardedSteps (fun s => P (.trial c s)) (kernel c) (2*Moment.probes)
          (Trial.initial (States.Mass.depth N) (rootInput c)) tr
          (Trial.nodeTicks (2*Moment.probes) (States.Mass.depth N)+tr.length) stop ∧
        Trial.step (kernel c) (2*Moment.probes) stop = .halt (packRound p.experts.length round)

private theorem warm_marked {N R T : ℕ} {P : PC → Prop} {a : Fin N} (mark : CampaignMarks R T a P)
    (left t : ℕ) (elapsed : t + left = T) (p : Population N) (positive : ℕ)
    (good : mark.HistoryGood t p positive) {tr bit}
    (run : Trial.Emits (stream (Learning.Pool.batch N R) (Campaign.runRound R (commonMarkets N)) a T left p positive) tr bit) :
    ∃ last, GuardedRun P (.campaign (sourceCursor R T left a p positive)) tr
        (left * (Trial.nodeTicks (2*Moment.probes) (States.Mass.depth N) + 2) + tr.length) (.campaign last) ∧
      step (.campaign last) = .halt bit ∧ DimensionAt N (.campaign last) := by
  induction left generalizing t p positive tr bit with
  | zero =>
    cases run
    let c := sourceCursor R T 0 a p positive
    have atEnd : T-t=0 := by omega
    have outer : P (.campaign c) := by simpa only [atEnd] using mark.outer t (by omega) p positive good
    refine ⟨c,⟨?_,outer⟩,?_,rfl⟩
    · simpa using GuardedSteps.refl (P := P) (.campaign c)
    · simp [c,sourceCursor,step,campaignBoundary,stateOf]
  | succ n ih =>
    rw [stream] at run
    obtain ⟨first,round,tail,rfl,e,eLater⟩ := run.bind_inv
    have tlt : t < T := by omega
    have leftEq : T-t=n+1 := by omega
    let c := sourceCursor R T (n+1) a p positive
    have outer : P (.campaign c) := by simpa only [leftEq] using mark.outer t tlt.le p positive good
    obtain ⟨stop,inner,halt⟩ := mark.inner t tlt p positive good e
    rw [leftEq] at inner halt
    have one := guarded_round_of_marked_root (c:=c) (Nat.zero_lt_succ n) outer inner halt
    have next : finishRound c (packRound p.experts.length round) = _ := finish_sourceCursor R T n a p positive round
    rw [next] at one
    obtain ⟨last,later,done,dim⟩ := ih (t+1) (by omega) _ _ (mark.advance t tlt p positive good e) eLater
    have all := one.trans later.steps
    refine ⟨last,⟨?_,later.endpoint⟩,done,dim⟩
    convert all using 1
    simp only [c,sourceCursor,List.length_append,Nat.succ_mul]
    omega

/-- Accumulate state invariants along every arbitrary-reply trace, including its
final physical state. -/
theorem campaign_marked_run {N R T : ℕ} {P : PC → Prop} {a : Fin N} (marks : CampaignMarks R T a P)
    {tr bit} (hr : Trial.Emits (Computation.ofTree (Campaign.strategy R T a (commonMarkets N))) tr bit) :
    ∃ last, GuardedRun P (.campaign (startCampaign N R a.val T)) tr
        (T * (Trial.nodeTicks (2*Moment.probes) (States.Mass.depth N) + 2) + tr.length) (.campaign last) ∧
      step (.campaign last) = .halt bit ∧ DimensionAt N (.campaign last) := by
  rw [← stream_eq_strategy,ofTree_toTree] at hr
  obtain ⟨last,path,finished,dim⟩ := warm_marked marks T 0 (by simp) _ _ marks.initial hr
  have start : startCampaign N R a.val T = sourceCursor R T T a (.start (Learning.Pool.batch N R)) 0 :=
    congrArg (fun s => CampaignCursor.mk N R a.val T T s) (startCampaign_state N R a.val T)
  exact ⟨last,start ▸ path,finished,dim⟩

end Driver
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI

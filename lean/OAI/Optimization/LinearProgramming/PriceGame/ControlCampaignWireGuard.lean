import OAI.Optimization.LinearProgramming.PriceGame.ControlCampaignWireHistory
import OAI.Optimization.LinearProgramming.PriceGame.ControlCampaignMarkedSource
import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialRoundWidth
import OAI.Optimization.LinearProgramming.PriceGame.FixedShareCombinedWire

/-! One polynomial bounds the complete first-order control state at every step,
on every public campaign transcript, including all nested adaptive market trials. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Wire

open Campaign

attribute [local irreducible] Moment.probes runRound TrialExecution.runReference
  TrialExecution.run TrialExecution.execute

private noncomputable def campaignWidthMarks {N : ℕ} (a : Fin N) (R T : ℕ) (hT : T ≤ (N+R.size+1)^300) :
    Driver.CampaignMarks R T a (fun pc => (combinedCode pc).length ≤ combinedPolynomial.eval (inputSize N R)) where
  HistoryGood := HistoryGood a R T
  initial := historyGood_start a R T
  advance := by
    intro t ht p positive good tr round e
    exact HistoryGood.advance good ht e
  outer := by
    intro t ht p positive good
    obtain ⟨old,rfl,rfl,prior⟩ := good
    exact (combined_campaign_length _ (sourceCursor_length_prefix a R T t ht old prior)).trans
      (combined_campaign_polynomial N R T hT)
  inner := by
    intro t ht p positive good tr round e
    obtain ⟨old,rfl,rfl,prior⟩ := good
    have cursor := sourceCursor_length_prefix a R T t ht.le old prior
    obtain ⟨stop,states,halt⟩ := run_round_guarded_width a R T hT old t ht.le
      (fun j hj => (prior j hj).2) (votesBefore a old t) e
    exact ⟨stop,states.weaken (fun s hs => (combined_trial_length _ s cursor hs).trans
      (combined_trial_polynomial N R T hT)),halt⟩

set_option exponentiation.threshold 300 in
/-- The public horizon and the physical word polynomial are fixed independently
of the labels. The terminal program counter satisfies the same bound. -/
theorem campaign_uniform_guard (i : PublicInput) :
    Native.Replay.SourceRuns i (fun pc =>
      (combinedCode pc).length ≤ combinedPolynomial.eval (inputSize i.goods i.range)) :=
  Native.Replay.sourceRuns_of_marks i (campaignWidthMarks i.anchor i.range (rounds i.goods i.range)
    (rounds_eq i.goods i.range).le)

end Wire
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI

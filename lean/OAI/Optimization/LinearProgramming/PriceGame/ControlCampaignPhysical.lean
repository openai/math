import OAI.Optimization.LinearProgramming.PriceGame.ControlCampaignInner
import OAI.Optimization.LinearProgramming.PriceGame.ControlPhysicalPhase

/-! # Exact physical transition along every executed source campaign instruction -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Driver

open Native (TrialGlobals TrialKernel)

/-- A single guarded trial compiler gives equality between the actual finite
physical microprogram and the source instruction everywhere along each possible
campaign transcript, including its halting instruction. -/
theorem physical_campaign_trace {N R T : ℕ} (ops : TrialGlobals → TrialKernel)
    (compiled : InnerRoundCompiler N R (Native.innerAgrees ops)) (a : Fin N) {tr bit}
    (hr : Trial.Emits (Computation.ofTree (Campaign.strategy R T a (commonMarkets N))) tr bit) :
    ∃ last, GuardedRun (fun pc => Native.physicalMicro ops (N,pc) = step pc)
        (.campaign (startCampaign N R a.val T)) tr
        (T * (Trial.nodeTicks (2*Moment.probes) (States.Mass.depth N) + 2) + tr.length) (.campaign last) ∧
      step (.campaign last) = .halt bit ∧ DimensionAt N (.campaign last) ∧
      Native.physicalMicro ops (N,.campaign last) = .halt bit := by
  obtain ⟨last,good,done,dim⟩ := campaign_guarded_steps (full_guarded_compiler compiled) a hr
  have endEq := Native.physicalMicro_agrees ops N (.campaign last) trivial dim trivial
  refine ⟨last,⟨?_,endEq⟩,done,dim,endEq.trans done⟩
  exact good.mono fun pc h => Native.physicalMicro_agrees ops N pc h.1.1 h.1.2 h.2

end Driver
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI

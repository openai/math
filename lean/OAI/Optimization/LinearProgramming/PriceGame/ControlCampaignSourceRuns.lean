import OAI.Optimization.LinearProgramming.PriceGame.ControlCampaignPhysical
import OAI.Optimization.LinearProgramming.PriceGame.ControlReplaySource

/-! # Direct source-run contracts used by the physical finite-tape replay -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Native
namespace Replay

/-- The equality to the physical microprogram includes the very last dispatch. -/
theorem sourceRuns_physical (ops : TrialGlobals → TrialKernel) (i : PublicInput)
    (inner : Driver.InnerRoundCompiler i.goods i.range (innerAgrees ops)) :
    SourceRuns i (fun pc => physicalMicro ops (i.goods,pc) = Driver.step pc) := by
  intro tr b source
  obtain ⟨last,good,stop,_,_⟩ := Driver.physical_campaign_trace ops inner i.anchor source
  exact ⟨.campaign last,good,stop⟩

end Replay
end Native
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI

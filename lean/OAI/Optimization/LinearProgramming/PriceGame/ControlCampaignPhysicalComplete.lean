import OAI.Optimization.LinearProgramming.PriceGame.ControlCampaignSourceRuns
import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialNativeCorrect

/-! # Closed arbitrary-reply refinement of the physical campaign program -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Driver

/-- The concrete clipped physical trial kernel satisfies the live guards required
at all recursive instructions of every genuinely sourced outer round. -/
theorem boundedInnerCompiler {N R : ℕ} (hN : 0<N) :
    InnerRoundCompiler N R (Native.innerAgrees Native.boundedTrialKernel) := by
  apply innerRoundCompiler_of_root
  intro ne experts w hw tr out emit
  exact Native.boundedTrial_guarded hN experts w hw emit

end Driver
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Native
namespace Replay

/-- Every actual source transcript runs through the physical microprogram with
the source state and halting bit at all instructions, including the terminal one. -/
theorem physicalSourceRuns (i : PublicInput) :
    SourceRuns i (fun pc => physicalMicro boundedTrialKernel (i.goods,pc) = Driver.step pc) :=
  sourceRuns_physical boundedTrialKernel i (Driver.boundedInnerCompiler (Nat.zero_lt_of_lt i.anchor.isLt))

end Replay
end Native
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI

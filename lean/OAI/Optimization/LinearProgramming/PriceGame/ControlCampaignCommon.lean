import OAI.Optimization.LinearProgramming.PriceGame.ControlCampaignNative
import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialRefinement

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Driver

/-- The transcript compiler is witnessed by the actual common-unit root trial. -/
theorem commonRoundCompilation (N R : ℕ) : RoundCompilation N R :=
  roundCompilation_of_root R (fun experts w hw _ _ e => Trial.run_common_refines experts w hw e)

end Driver
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI

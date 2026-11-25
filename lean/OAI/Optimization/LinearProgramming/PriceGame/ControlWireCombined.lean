import OAI.Optimization.LinearProgramming.PriceGame.ControlWireCampaign
import OAI.Optimization.LinearProgramming.PriceGame.ControlWireState
import OAI.Optimization.LinearProgramming.PriceGame.ControlCampaignDriver

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Wire

open ExactQuantumFactoring.BitStackProgram

/-- The suspended outer loop appears once, followed, in trial mode, by the active stack. -/
def combinedCode : Driver.PC → List Bool
  | .campaign c => false :: campaignCursorCode c
  | .trial c s => true :: prodCode campaignCursorCode stateCode (c,s)

end Wire
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI

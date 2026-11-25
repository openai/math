import OAI.Optimization.LinearProgramming.PriceGame.ControlCampaignMarked
import OAI.Optimization.LinearProgramming.PriceGame.ControlReplaySource

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Native
namespace Replay

/-- Any checked elapsed-history width invariant on actual source trials supplies
the exact state-word-bound contract required by the physical replay compiler. -/
theorem sourceRuns_of_marks (i : PublicInput) {P : Driver.PC → Prop}
    (m : Driver.CampaignMarks i.range (Campaign.rounds i.goods i.range) i.anchor P) : SourceRuns i P := by
  intro tr b source
  obtain ⟨last,good,stop,_⟩ := Driver.campaign_marked_run m source
  exact ⟨.campaign last,good,stop⟩

end Replay
end Native
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI

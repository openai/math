import OAI.Computability.BorderVNP.DiagonalCalendarOriginalReportSelection
import OAI.Computability.BorderVNP.DiagonalCalendarOriginalSelectionCharge

/-! # The native paid report operation at an original lookup site -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta

set_option cleanup.letToHave false
set_option maxHeartbeats 8000000
set_option maxRecDepth 18000

private def selectObservedCharge := SignedCalendarAt.onEarlierReportedSite
  ``SignedCalendarAt.chargeReportAtOriginalSelection

local elab "observedChargeStatement%" : term => do inferType (← selectObservedCharge)
/-- The report operator on the physical field selected from this returned family. -/
abbrev SignedCalendarAt.ChargeAtEarlierReportedSite : Prop := observedChargeStatement%
/-- Feed the true selected frame and exterior of each returned field to its clock proof. -/
theorem SignedCalendarAt.chargeAtEarlierReportedSite : SignedCalendarAt.ChargeAtEarlierReportedSite := by
  run_tac
    (← Lean.Elab.Tactic.getMainGoal).assign (← selectObservedCharge)
    Lean.Elab.Tactic.replaceMainGoal []

end Diagonal

end BorderVNP
end Computability
end OAI

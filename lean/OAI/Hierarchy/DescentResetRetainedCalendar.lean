import OAI.Hierarchy.DescentResetRetainedCalendarWidths
import OAI.Hierarchy.DescentDenseHostOrder

namespace OAI
/-! # The real static stem and fallback shape roster at a reset -/
namespace Hierarchy.DescentSixParty.AtomSchedule
noncomputable section
variable (S : DescentCompiler.AtomSchedule)
variable {n d : ℕ} (board : NonlinearExpanders.Graph n d)
/-- The same static shape roster and host bounds used by the genuine compact actor directory. -/
def retainedPlacementCalendar (k age Ht M : ℕ) : DescentResetRetainedPlacement.Chart :=
  ⟨S.hostSize age,S.hostSize (age+1),(DescentDenseHostOrder.roster board k Ht).card,S.groupCount (age+1),2^k,M⟩

end
end Hierarchy.DescentSixParty.AtomSchedule

end OAI

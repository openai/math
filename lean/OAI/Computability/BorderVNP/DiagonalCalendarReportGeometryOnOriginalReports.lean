import OAI.Computability.BorderVNP.DiagonalCalendarCandidateOnOriginalReports
import OAI.Computability.BorderVNP.DiagonalRegisteredNativeGeometryTerms

/-! # The native geometry on the original reported prefixes -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

set_option maxRecDepth 22000
set_option maxHeartbeats 16000000
set_option cleanup.letToHave false

local elab "geometryOnOriginalReports%" : term =>
  SignedCalendarAt.geometryOnCandidateFields ``SignedCalendarAt.reportedCandidateOnOriginalReports

private noncomputable def originalReportGeometryFields : PSigma (fun claim : Prop => claim) :=
  ⟨_,geometryOnOriginalReports%⟩

/-- For each originally reported field and team, the native signed reporter
retains the network's cable rows, its supplied width at every cell, and the
bank address chosen for that cell. -/
theorem SignedCalendarAt.reportGeometryOnOriginalReports : originalReportGeometryFields.1 :=
  originalReportGeometryFields.2

end Diagonal

end BorderVNP
end Computability
end OAI

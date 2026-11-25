import OAI.Computability.BorderVNP.DiagonalCalendarReportProgramTerm
import OAI.Computability.BorderVNP.DiagonalCalendarRequestsOnOriginalStoredReports
import OAI.Computability.BorderVNP.DiagonalCalendarRunsOnOriginalStoredReports
import OAI.Computability.BorderVNP.DiagonalCalendarSiteOnStoredOriginalReports

/-! # Native execution on the original funded reports of one calendar pin -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal
open Lean Meta Elab Term

set_option maxHeartbeats 9000000
set_option maxRecDepth 24000
set_option cleanup.letToHave false

local elab "storedPhysicalProgram%" : term => do
  return ← SignedCalendarAt.checkedOriginalReportProgram
    ``SignedCalendarAt.siteDataOnStoredReportsAtOriginalInputs
    ``SignedCalendarAt.requestsOnOriginalStoredReports
    ``SignedCalendarAt.runsOnOriginalStoredReports true

set_option Elab.async false in
private noncomputable def storedProgram : (Result : Type 1) ×' Result := storedPhysicalProgram%

/-- The original raw reports and one family of funded returns on that pin yield the complete
native execution. The site, its paid writer and its measured run use those same returns. -/
noncomputable def SignedCalendarAt.executionOnStoredOriginalReports : storedProgram.1 :=
  storedProgram.2

end Diagonal

end BorderVNP
end Computability
end OAI

import OAI.Computability.BorderVNP.DiagonalCalendarReturnedMarkers
import OAI.Computability.BorderVNP.DiagonalTallyReportAllocatedWrites

/-! # Selecting the funded reader on the bank that received the report -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta Elab Term DiagonalTallyCellReports

/-- Apply the registered funded reader to one field and team using the physical
bank named in the allocation and the memory named in the marker observation. -/
elab (name := registeredFundedRead)
    "registeredFundedRead% " reader:term:max field:term:max team:term:max
    allocation:term:max marker:term:max : term => do
  let read ← elabTerm reader none
  let f ← elabTerm field none
  let u ← elabTerm team none
  let allocated ← elabTerm allocation none
  let marked ← elabTerm marker none
  let some layout ← whnfUntil (← inferType allocated) ``ReportAllocation |
    throwErrorAt allocation "expected a returned report allocation"
  let #[_, _, banks, _, _, _] := layout.getAppArgs |
    throwErrorAt allocation "expected the bank of the allocated report"
  let some observation ← whnfUntil (← inferType marked) ``SignedCalendarAt.frozenIssuedMarkers |
    throwErrorAt marker "expected the marker observation on the returned memory"
  return mkAppN read #[f, u, banks, observation.getAppArgs.back!, marked]

end Diagonal

end BorderVNP
end Computability
end OAI

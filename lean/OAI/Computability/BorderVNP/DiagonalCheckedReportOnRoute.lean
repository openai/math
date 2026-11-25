import OAI.Computability.BorderVNP.DiagonalCheckedRouteReadback

/-! # The reached reports at a checked calendar declaration -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Elab Term

/-- The report conjunct of the actual selected frame at its admitted
declaration. Keep the observed route's proof on the same exterior. -/
elab "returnedReportOnRoute% " readback:term:max declaration:term:max
    admission:term:max route:term:max : term => do
  let found ← elabTerm readback none
  let publicWord ← elabTerm declaration none
  let accepts ← elabTerm admission none
  let selected ← elabTerm route none
  let event := mkApp2 (mkProj ``CheckedRouteReadback 2 found) publicWord (mkApp accepts selected)
  return mkProj ``And 0 event

end Diagonal

end BorderVNP
end Computability
end OAI

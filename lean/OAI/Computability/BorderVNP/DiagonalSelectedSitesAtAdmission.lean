import OAI.Computability.BorderVNP.DiagonalCheckedRouteReadback

/-! # The selected sites at a registered route's admitted declaration -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal
open Lean Elab Term

/-- Apply the site family in a checked route readback at the actual declaration
and its admission proof. Its dependent frame stays the one chosen by the readback. -/
elab "selectedSitesOnRoute% " checked:term:max declaration:term:max
    admission:term:max route:term:max : term => do
  let found ← elabTerm checked none
  let word ← elabTerm declaration none
  let honest ← elabTerm admission none
  let selected ← elabTerm route none
  return mkApp2 (mkProj ``CheckedRouteReadback 1 found) word (mkApp honest selected)

end Diagonal

end BorderVNP
end Computability
end OAI

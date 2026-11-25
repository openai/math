import OAI.Computability.BorderVNP.CubeISAOwnedPrepare
import OAI.Computability.BorderVNP.CubeISAOwnedTraceScan
import OAI.Computability.BorderVNP.RoutingISARegisterFrame

/-! # Routed cursors through the singleton address and validity test -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Owned

/-- Even an unsuccessful label trial consumes no private choices and preserves both routed
stream cursors. The validity scan only examines the other-coordinate digits. -/
theorem singleCandidate_frame (n : ℕ) :
    (singleCandidate n).unsigned = true ∧ (singleCandidate n).keeps 36 = true ∧
      (singleCandidate n).keeps 37 = true := by
  induction n with
  | zero => decide
  | succ n ih => exact ih

end RoutingISA.Owned

end BorderVNP
end Computability
end OAI

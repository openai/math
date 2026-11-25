import Mathlib.Data.Nat.Log

namespace OAI
/-! # Public depth of the purchased reset table -/
namespace Hierarchy.DescentFineTerminals
/-- The merged-hub route can depend on the fixed ratio of hub and grouping
scales. The core coefficient uses only the nonhub branch. -/
def terminalDepth (Δ Y f g : ℕ) (ordinary : Bool) : ℕ :=
  if ordinary then 36*Nat.clog 2 (2*Δ*Y)
  else Nat.clog 2 (Δ*((32*Nat.clog 2 (2*Δ)+1+2*2^(g-f))*Y))
end Hierarchy.DescentFineTerminals

namespace Hierarchy.DescentSixParty.GroupStage
open DescentFineTerminals
def depthBound (deg n f g : ℕ) := 2*max (terminalDepth deg (2^n) f g false) (terminalDepth deg (2^n) f g true)
end Hierarchy.DescentSixParty.GroupStage

end OAI

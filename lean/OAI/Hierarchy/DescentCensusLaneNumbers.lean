import Mathlib

namespace OAI
/-! # Public bit widths of the signed census and ordinary chooser -/

namespace Hierarchy.DescentPackedColony.Phase
def unit (k b : ℕ) := 2*(1+k*2^k)+b*2^k+(k+3)
end Hierarchy.DescentPackedColony.Phase

namespace Hierarchy.DescentPackedColony.Phase
def recordWidth (k b cap : ℕ) := max (unit k b) ((1+b+2*cap)*2^k)
end Hierarchy.DescentPackedColony.Phase

end OAI

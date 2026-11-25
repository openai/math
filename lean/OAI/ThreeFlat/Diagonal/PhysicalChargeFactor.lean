import Mathlib.Data.Nat.Basic

namespace OAI
/-! # The fixed cost factor for a physical shrink stage -/

namespace ThreeFlat.Diagonal.PhysicalStage

def shrinkChargeFactor (s : ℕ) := 3+6*(2^s+1)

end ThreeFlat.Diagonal.PhysicalStage

end OAI

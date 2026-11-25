import Mathlib.Data.Nat.Basic

namespace OAI
/-! # Uniform stage price for the resources of a terminal tree -/

namespace ThreeFlat.Diagonal.PhysicalStage
def Run.treeFee (K depth : ℕ) := (2*depth+1)*K
end ThreeFlat.Diagonal.PhysicalStage

end OAI

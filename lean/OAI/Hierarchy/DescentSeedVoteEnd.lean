import OAI.Hierarchy.DescentSeedHeaderFloorNumbers

namespace OAI
/-! # End of the physically allocated sequence of vote counters -/
namespace Hierarchy.DescentPackedEpochShelves
open DescentTerminalEpochChart
noncomputable section
variable {A : Type}

def finalAt (work lo r : ℕ) (ss : List (Source A)) :=
  work+((shelves r lo 0 ss).map (stepRows r)).sum

end
end Hierarchy.DescentPackedEpochShelves

end OAI

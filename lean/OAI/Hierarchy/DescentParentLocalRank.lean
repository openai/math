import OAI.Hierarchy.DescentHaloPairRanks

namespace OAI
/-! # The number of earlier distinct endpoints on a receiver's own header row -/
namespace Hierarchy.DescentParallelBase.ParentFilter
open DescentHaloWalkRAM
noncomputable section
variable {H D : ℕ}
local notation "P" => breadth D

/-- Header digit for a reachable site in the issuing donor's chart. -/
def localRank (R : Fin H→Fin D→Option (Fin H)) (v : Fin H) (p : Fin P) : Fin P:=
  ⟨Ranks.earlier (Rebase.terminal R) v (Rebase.terminal R v p),Ranks.bound _ _ _⟩

end
end Hierarchy.DescentParallelBase.ParentFilter

end OAI

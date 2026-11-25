import OAI.Hierarchy.DescentHaloRankProgram

namespace OAI
/-! # The two observations made at the terminus of one physical walk -/
namespace Hierarchy.DescentRawCablePanel
open DescentHaloWalkRAM
noncomputable section
variable {H D : ℕ} (roster : Fin H→Fin D→Option (Fin H)) (start : Fin H) (flag : Fin H→Bool)

/-- The two host-shared columns are indexed by the same native four-digit path.
A missing endpoint has false hub status and never supplies an active role. -/
def observedRank (p : Fin (breadth D)) : ℕ :=
  Ranks.earlier (DescentHaloCompilation.reached roster) start (DescentHaloCompilation.reached roster start p)
def observedHub (p : Fin (breadth D)) : Bool :=
  (walk roster start (path p) 4).elim false flag


end
end Hierarchy.DescentRawCablePanel

end OAI

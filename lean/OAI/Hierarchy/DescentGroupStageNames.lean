import OAI.Hierarchy.DescentNamedPlacement
import OAI.Hierarchy.DescentStageReindex
import OAI.Hierarchy.DescentGroupStage

namespace OAI
/-! # Carrying the ordinary placement and executable cable order through renaming -/

namespace Hierarchy.DescentSixParty.GroupStage
open DescentColonies PhysicalRename
open scoped Classical BigOperators
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
variable {d k : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {q ε : ℝ}

def afterNames {S : MarkedWorld F d P bits} (n : Normalize S) (A : GroupStage n.result G q ε J V k)
    (s : Equiv.Perm n.result.graph.Site) (e : Equiv.Perm n.result.graph.Edge) :
    GroupStage (n.appendNames s e).result G q ε J V k := (n.appendNames_result s e).symm ▸ A.names s e

end
end Hierarchy.DescentSixParty.GroupStage

end OAI

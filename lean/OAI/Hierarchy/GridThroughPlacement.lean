import OAI.Hierarchy.GridThroughPositions
import OAI.Hierarchy.GridThroughPaths
import OAI.Hierarchy.GridLensContraction

namespace OAI
/-! # The finite lens placement of an actual through program -/

namespace Hierarchy.GridThrough.Program
open UniversalGrid GridLens
noncomputable section

variable {F : Type*} [Field F] {k n p E : ℕ} (X : Catalyst.Approximation F k p)
variable (P : Program (Fin E) n p X.width)

/-- No geometric or price hypothesis is needed to mount a checked through
program. The address and route proofs use the very same emitted test list. -/
def placement (R : ℝ) :
    Placement X P.wiring P.direction R
      (fun u => GridDiagonal.focus R (P.direction u.1,u.2)) n where
  position := P.position R
  row := P.row
  cell := cellOrdinal.symm
  cell_eq := P.position_cell R
  focus := P.position_focus R
  paths := P.paths_of_positions R (P.addrPoint R) (P.wiring.edgeAt (P.position R))
    (P.position_edge R) (P.addrPoint_base R) (P.addrPoint_center R) (P.addrPoint_focus R)

end
end Hierarchy.GridThrough.Program

end OAI

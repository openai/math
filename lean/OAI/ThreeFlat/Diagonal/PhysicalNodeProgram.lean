import OAI.ThreeFlat.Diagonal.PhysicalNodeTape
import OAI.ThreeFlat.Diagonal.NavigationScalar
import OAI.ThreeFlat.Diagonal.NavigationCountedLoop
import OAI.ThreeFlat.Diagonal.PhysicalNodeBankLayout
import OAI.ThreeFlat.Diagonal.NavigationArchiveFields
import OAI.ThreeFlat.RAM.NavigationNodeRows
import OAI.ThreeFlat.RAM.PackedStageArchive

namespace OAI
/-! # Native chronological node registers and their compact sixteen-word stage headers -/

namespace ThreeFlat.Diagonal.NavigationPass
open Computability.VPVNP.BurstRAM RAM RAM.PhysicalProcedure RAM.NavigationNodeRows
open scoped Classical Fin.CommRing
variable {W : ℕ}

/-- The layer count changes with the requested diagonal size. The native loop executes
one compiled node/charge publisher and advances through its physically installed headers. -/
def NodeArchive.publish (a : NodeArchive) (count : ℕ) : Procedure W :=
  let image : PackedStageArchive.Layout := ⟨a.phase,a.rawHeader,a.rawHeader,a.headerBase,16*count⟩
  (PackedStageArchive.procedure image).seq
    ((start (a.banks.current : Word W) a.headerBase).seq ((start (a.counter : Word W) count).seq
      (loop (a.counter : Word W) (NavigationNodeRows.procedure a.banks a.childCap a.halfCap a.motifCap))))

end ThreeFlat.Diagonal.NavigationPass

end OAI

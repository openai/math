import OAI.Hierarchy.TraceReceiverPreparation
import OAI.Hierarchy.TraceReceiverMapHeader
import OAI.Hierarchy.TraceReceiverMapSave

namespace OAI
/-! # Native counted terminal pin-map publication -/
namespace Hierarchy.TraceReceiverTasks
open ThreeFlat RAM DescriptorExpr DescriptorScan
open Computability.VPVNP.BurstRAM PrivateRAM PhysicalProcedure
open scoped Classical Fin.CommRing
open RAM.TickTerminalRoot

variable {W : ℕ}

/-- One native counted body services every selected root; each body saves its
map before the next root can use the scratch arena. -/
def maps (W : ℕ) (A : Arena) (tasks header : ℕ) : Procedure W :=
  ((TraceReceiverMapSave.seed W header tasks A.control).seq
    (TraceReceiverMapSave.one W A header)).counted ((A.control+4:ℕ):Word W)

end Hierarchy.TraceReceiverTasks

end OAI

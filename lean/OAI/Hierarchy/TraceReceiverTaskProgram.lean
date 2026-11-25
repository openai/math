import OAI.Hierarchy.TraceReceiverBeforeShape
import OAI.Hierarchy.TraceReceiverMapShape
import OAI.Hierarchy.TraceReceiverTaskTime

namespace OAI
/-! # Hardware of terminal-root task preparation and saved-map publication -/
namespace Hierarchy.TraceReceiverTasks
open ThreeFlat RAM Computability.VPVNP.BurstRAM PrivateRAM PhysicalProcedure TickTerminalRoot

/-- Exact native hardware of the three width/prefix scans, task emitter and saved-map loop. -/
def hardware := beforeHardware+mapHardware

private theorem combine {W : ℕ} (a b : Procedure W) (x y : ℕ)
    (first : size a=x) (second : size b=y) :
    a.labels+a.registers+a.slots+b.labels+b.registers+b.slots=x+y := by
  unfold size at first second
  omega

theorem dimensions (W : ℕ) (D : Layout) (count cap : ℕ) (width : Fin 3 → ℕ)
    (A : Arena) (header : ℕ) :
    let a := before W D count cap width
    let b := maps W A D.tasks header
    a.labels+a.registers+a.slots+b.labels+b.registers+b.slots=hardware :=
  combine (before W D count cap width) (maps W A D.tasks header) beforeHardware mapHardware
    (before_size W D count cap width) (map_size W A D.tasks header)

end Hierarchy.TraceReceiverTasks

end OAI

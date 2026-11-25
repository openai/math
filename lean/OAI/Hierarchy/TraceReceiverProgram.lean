import OAI.Hierarchy.TraceReceiverFieldMachine
import OAI.Hierarchy.TraceReceiverCommands
import OAI.Hierarchy.GridPhysicalAdmission
import OAI.Hierarchy.TraceResourceNodeRegistration

namespace OAI
/-! # The common receiver executable and the field product of its selected sites -/

noncomputable section
namespace Hierarchy.TraceReceiverProgram

open ThreeFlat Diagonal RAM
open Computability.VPVNP.BurstRAM PrivateRAM NavigationPass NavigationDirectory RAM.NavigationNodeRows
open NodePublication TraceNodeHeaders PhysicalProcedure TraceAdmission TraceFactorReceiver
open TickWeightedBank BitLayout Contraction HistoryContraction
open scoped Classical BigOperators

/-- The public fixed layout of the two native archive scans. Every field is
determined before the selector or any of the local input pins is read. -/
structure Directory where
  archive : Archive
  stages : List Stage
  edges : ℕ
  repetitions : ℕ
  nodeControl : ℕ
  registerHeader : ℕ
  registrationLimit : ℕ
  resourceBase : ℕ
  node : NodeArchive
  seedLayer : Layer
  parameters : Resources.Parameters ℕ

/-- First initialize the selected journal from the compact T directory; read
back that journal and publish charged physical records and the owner table. -/
def navigation {F : Type} [Field F] [Fintype F] (B : PhysicalStage.Block F) (W : ℕ)
    (dir : Directory) : Procedure W :=
  (GridPhysicalAdmission.program B dir.archive dir.stages dir.edges W dir.repetitions).seq
    (Resources.registerNodes W dir.nodeControl dir.registerHeader dir.registrationLimit dir.archive.cursor.header
      dir.stages.length dir.resourceBase dir.node dir.seedLayer dir.parameters)

/-- Select the current tick's roots, execute their sparse stage compiler, save
their pin maps and row offsets, then expand the five-word tasks to the actual
seven-word gather commands in RAM. -/
def sources {F : Type} [Field F] [Fintype F] (B : PhysicalStage.Block F) {W : ℕ}
    (dir : Directory) (select compileRoots publishTasks : Procedure W)
    (current commands tasks : ℕ) : Procedure W :=
  (navigation B W dir).seq (select.seq (compileRoots.seq
    (publishTasks.seq (Commands.procedure W current commands tasks))))

end Hierarchy.TraceReceiverProgram
end

end OAI

import OAI.Hierarchy.GridChosenReceiverMapReturn
import OAI.Hierarchy.GridChosenReceiverRestore
import OAI.Hierarchy.TraceReceiverRestoredWriter

namespace OAI
/-! # The restored-roster and command-writer instruction blocks of the installed T -/

noncomputable section
namespace Hierarchy.GridChosenReceiver
open ThreeFlat Diagonal Diagonal.HistoryContraction Diagonal.PhysicalStage
open RAM RAM.PhysicalProcedure RAM.TickTerminalRoot Computability.VPVNP.BurstRAM PrivateRAM
open TraceDistribution GridScale GridThrough GridRegisteredSetting GridInstalledEvaluator
open TraceFactorReceiver TraceFactorReceiver.Gather
open scoped BigOperators Classical

variable {F : Type} [Field F] [Fintype F] {w pc rr pp S base fuel axes : ℕ}
variable (D : RunData F (64*w) pc rr pp S base fuel axes (w/2)) (l : GridNativeImage.Layout)
set_option quotPrecheck false
local notation "W" => (64*w)
local notation "V" => TraceAdmission.receiverAge w
local notation "dir" => GridReceiverDirectory.native D l
local notation "p" => (dir).parameters
local notation "A" => GridReceiverBanks.arena D l

def writeTerminal : Procedure W :=
  let b:=GridReceiverBanks.tasks w
  let c:=(A).control+1
  let commands:=GridReceiverBanks.commands w
  let cursor:=GridReceiverBanks.cursor w
  let count:=GridReceiverBanks.limit w
  (TraceAdmission.Resources.mount W b.parent [(A).metadata,(A).physicalPins,0,0]).seq
    ((TraceReceiverTasks.before W b c count (GridReceiverBanks.width w)).seq
      ((TraceReceiverTasks.maps W A b.tasks (GridReceiverBanks.mapHeader w)).seq
        ((TraceReceiverTasks.rangeSeed W b.current c commands 0 7).seq
          ((TraceFactorReceiver.Commands.procedure W b.current commands b.tasks).seq
            (TraceFactorReceiver.Cursor.program W cursor commands c)))))

theorem terminal_parts :
    terminal D l=
      (GridReceiverTickDirectory.build (GridReceiverTickDirectory.banks w V) W
        (2+SelfAdvice.textSize W pc pp) (p).roots
        (((20*(w+1)+2)^((l.dimension+1)+2))*(p).roots)).seq (writeTerminal D l) := rfl

end Hierarchy.GridChosenReceiver
end

end OAI

import OAI.Hierarchy.GridChosenReceiverStartup
import OAI.Hierarchy.GridChosenReceiverPrefix
import OAI.Hierarchy.TraceReceiverDescendantExecution

namespace OAI
/-! # Fixed work of the two receiver elections and the mounted terminal job -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.GridChosenReceiver
open ThreeFlat Diagonal PhysicalStage RAM NavigationPass
open GridRegisteredSetting Computability.VPVNP.BurstRAM PrivateRAM

variable {F : Type} [Field F] [Fintype F] {w pc regs slots S base fuel axes : ℕ}
variable (D : RunData F (64*w) pc regs slots S base fuel axes (w/2)) (l : GridNativeImage.Layout)
local notation "directory" => GridReceiverDirectory.native D l
local notation "first" => (directory).parameters.firstFinal
local notation "rootCount" => (directory).parameters.roots
local notation "dimension" => ((l.dimension+1)+2)
local notation "layoutPlan" => GridReceiverBanks.pinPlan D l
local notation "electionClock" => GridReceiverTickDirectory.clock (64*w)
  (((20*(w+1)+2)^dimension)*rootCount)

/-- The first prefix runs the ordinary classifier and its class-major root scan.
The second scan rebuilds the selected root list. The four chronological cut
allowances also cover the fixed terminal and gather headers at these widths. -/
theorem spending_setup (age : 10≤w) :
    28+16*l.pinWidth+(GridReceiverDirectory.prefixTime D l+
      (TraceReceiverDescendantExecution.cost D first rootCount layoutPlan (17+24*(first+rootCount))+
        (electionClock+(4232+TraceReceiverTasks.before_clock 0)))) ≤ setupTime D l := by
  have mature : (64:ℕ)≤2^(3*w/5) :=
    Nat.pow_le_pow_right (n:=2) (by decide) (show 6≤3*w/5 by omega)
  have nativeArchive : (directory).archive = GridReceiverDirectory.archive D l := rfl
  dsimp only [setupTime,GridReceiverClock.scans,GridReceiverClock.startupTime,
    GridReceiverDirectory.prefixTime,TraceReceiverDescendantExecution.cost,
    TraceReceiverTablesMount.decodeWork,TraceReceiverTablesMount.libWork]
  rw [nativeArchive]
  omega

end Hierarchy.GridChosenReceiver
end

end OAI

import OAI.Hierarchy.TraceReceiverChargePrice
import OAI.Hierarchy.TraceReceiverMapProgram

namespace OAI
/-! # Fixed rate for the actual numerical task publisher and saved pin maps -/
namespace Hierarchy.TraceFactorReceiver.Gather
open ThreeFlat RAM Computability.VPVNP.BurstRAM PrivateRAM
open TraceDistribution

def seedPrice := 4+3*(2*(TraceReceiverMapSave.seedWord 1 0 0 0).binds+4)+20

def perRoot := TraceReceiverTasks.before_per_root+seedPrice

def fullRate (stageRate perLevel : ℕ) := stageRate+(perRoot+44)+perLevel

/-- The cost proportional to the number of roots in the pre-scan is charged
to those same roots. The constant is incurred even by a tick with no roots. -/
theorem task_map_additions (n ports : ℕ) :
    TraceReceiverTasks.before_clock n+seedPrice*n+22*ports =
      TraceReceiverTasks.before_clock 0+perRoot*n+22*ports := by
  rw [TraceReceiverTasks.before_rate n,perRoot,Nat.add_mul]
  omega

theorem full_rate (w depth degree stages coefficient stageRate rootRate : ℕ)
    (perLevel price charge ports : ℕ) (height : depth≤ stages+4) (k : 0<coefficient)
    (positive : 0<charge) (localPins : ports≤2*charge)
    (covered : price≤FactorWork.archiveTariff w depth (setupPrice stages stageRate)
      (mapPrice degree rootRate) stages coefficient*charge) :
    price+(perRoot+22*ports)+perLevel*depth*charge ≤
      FactorWork.archiveTariff w depth (setupPrice stages (fullRate stageRate perLevel))
        (mapPrice degree rootRate) stages coefficient*charge :=
  charged_maps w depth degree stages coefficient stageRate rootRate perRoot perLevel price charge ports
    height k positive localPins covered

end Hierarchy.TraceFactorReceiver.Gather

end OAI

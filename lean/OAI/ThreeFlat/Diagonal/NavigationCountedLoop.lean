import OAI.ThreeFlat.RAM.CountedProcedure
import OAI.ThreeFlat.RAM.PhysicalProcedureSize

namespace OAI
/-! # Native hardware size of a counted navigation loop -/
namespace ThreeFlat.Diagonal.NavigationPass
open Computability.VPVNP.BurstRAM RAM.PhysicalProcedure RAM.HistoryStageBody.Physical
noncomputable section
variable {W : ℕ}

def loop (counter : Word W) (body : Procedure W) : Procedure W := body.counted counter

theorem loop_size (t : Procedure W) (c : Word W) :
    resources (loop c t)=10+resources t := by
  simp only [loop,Procedure.counted,resources]
  omega

end
end ThreeFlat.Diagonal.NavigationPass

end OAI

import OAI.ThreeFlat.RAM.HistorySelectedNodes
import OAI.ThreeFlat.RAM.TickPhysicalABI

namespace OAI
/-! # The six physical directory words used by the selected-node guard -/
namespace ThreeFlat.RAM.HistoryStageBody.Physical
open Computability.VPVNP.BurstRAM Diagonal.TickWorkspace
open scoped Fin.CommRing

def ownerData (W u : ℕ) : HistoryNodeDirectory.Selected.Data W :=
  fun i => ((![base u 18,base u 45,TickPhysicalABI.directory u 1,base u 1,
    TickPhysicalABI.directory u 3,base u 6+1] i : ℕ) : Word W)

end ThreeFlat.RAM.HistoryStageBody.Physical

end OAI

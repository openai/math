import OAI.ThreeFlat.Diagonal.PhysicalArchiveRowFields
import OAI.ThreeFlat.RAM.HistoryNodeDirectoryRow
import OAI.ThreeFlat.Diagonal.TickScratchRegion

namespace OAI
/-! # The registered receiver state read by selected native stage kernels -/

namespace ThreeFlat.Diagonal.NavigationPass.NativeNavigation
open Computability.VPVNP.BurstRAM PrivateRAM RAM PhysicalStage NodePublication NavigationNodeRows TickWorkspace HistoryStageSetup
open scoped Fin.CommRing
variable {W : ℕ}

structure WarmSources (age : ℕ) (banks : Banks) (rows : List NodeRow) (mid out warm : Memory W) : Prop where
  journal : ∀ i,base age 20 ≤ i→i<base age 40→warm i=mid i
  seedMetadata : ∀ i,base age 49 ≤ i→i<base age 53→warm i=mid i
  published : ∀ i,base age 43 ≤ i→i<base age 45→warm i=out i
  kind : ∀ q∈rows,∀ j : Fin q.layer.count,warm (banks.nodes+8*(q.layer.first+j.val))=(q.layer.kind:Word W)
  directory : ∀ q∈rows,∀ j : Fin q.layer.count,DirectoryRow banks q.layer j warm

end ThreeFlat.Diagonal.NavigationPass.NativeNavigation

end OAI

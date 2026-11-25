import OAI.Hierarchy.GridReceiverDirectoryROM
import OAI.Hierarchy.GridSimulationAssign
import OAI.Hierarchy.FactorOccurrences
import OAI.ThreeFlat.Diagonal.TickScratchRegion

namespace OAI
/-! # Framing the chronological rows through the native classifier and root list -/
namespace Hierarchy.GridReceiverTickDirectory
open ThreeFlat RAM Diagonal
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing

def banks (w v : ℕ) : Banks :=
  ⟨(GridPinArena.assignmentBanks w).keys,(GridPinArena.assignmentBanks w).output,
    TickWorkspace.base v 17,TickWorkspace.base v 18,15*GridDescription.sector w+20*GridPinArena.slab w⟩

/-- All unselected low-numbered tick-workspace pages, in particular S43
and S44, retain their value before both the classifier and root compactor. -/
theorem outside_receiver {w v N d T : ℕ} (ht : 0 < T) (cost : Fin N → Fin d → ℕ)
    (t : Fin T) {input mid out : Memory (64*w)} (reg : GridSimulation.Assigned ht cost input mid)
    (pub : Ticked (banks w v) (FactorAllocation.factors w cost (List.finRange N) t) (t.val:Word (64*w)) mid out)
    (a : ℕ) (low : a < 14*GridDescription.sector w)
    (roots : a < TickWorkspace.base v 17 ∨ TickWorkspace.base v 17 +
      (FactorAllocation.factors w cost (List.finRange N) t).length ≤ a)
    (controls : a < TickWorkspace.base v 18 ∨ TickWorkspace.base v 18+5 ≤ a) : out a=input a := by
  rw [pub.frame a roots controls (.inl (by change a < 15*GridDescription.sector w+20*GridPinArena.slab w; omega))]
  apply reg.frame
  unfold GridSimulation.protectedAddress FactorBucketRAM.untouched FactorBucketRAM.Outside
  dsimp [GridPinArena.assignmentBanks];omega

end Hierarchy.GridReceiverTickDirectory

end OAI

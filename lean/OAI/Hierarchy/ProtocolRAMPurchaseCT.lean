import OAI.Hierarchy.ProtocolRAMPurchaseMeasured
import OAI.Hierarchy.ProtocolRAMPurchaseSignedAllocation
import OAI.Hierarchy.ProbeStagePublicGroups

namespace OAI
/-! # The occupied-bank interface of the actual subdivision program

Procedure addresses, group counts and socket spans use the public fabric.
The CPU's group numbers enter only as values read from the three live banks;
any numbering of the finite group has the same mathematical purchases.
-/

namespace Hierarchy.ProtocolRAM.PurchaseCT
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native ProtocolRAMPurchaseAllocation
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing Classical
noncomputable section
variable {z d w k : ℕ}

/-- Eliminate all three geometric contents assumptions using the verified
subdivision output, including the center stage when the recursion is empty. -/
theorem resident (π : Equiv.Perm (Fin (2^z))) (t : StageAt z d) (start D depth first : ℕ)
    (input : Memory (wordBits z d copies)) (done : After (d:=d) π input (rounds d)) :
    ∃ enc : (stageAt z d t).Group ↪ Fin (Fintype.card (stageAt z d t).Group),
      (allocation t start D depth first).CTLoaded (banks t) (advisedStage z d π t) enc
        (images z d input (rounds d)) := by
  exact ⟨(groupNumber t).toEmbedding,resident_numbered π t start D depth first input done⟩

end
end Hierarchy.ProtocolRAM.PurchaseCT

end OAI

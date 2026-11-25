import OAI.ThreeFlat.RAM.HistorySelectedOwnerData
import OAI.ThreeFlat.RAM.HistorySelectedOwners
import OAI.ThreeFlat.RAM.HistoryNodeValue

namespace OAI
/-! # The selected node directory and the data published at each visited node -/
namespace ThreeFlat.RAM.HistoryStageBody.Physical
open Computability.VPVNP.BurstRAM PrivateRAM HistoryNodeDirectory.Selected
open scoped Fin.CommRing
variable {F : Type*} {W n : ℕ}

/-- The selection is fixed by the S45 roots and the S11 group/slot array.
The invariant records exactly the nodes this slot has already visited. -/
structure Ledger (u : ℕ) (D : Directory W n) (id : ((Fin 3→Bool)→F)→ℕ) (v : Fin n→NodeValue F)
    (keep : ℕ→Prop) (input : Memory W) (next : ℕ) (m : Memory W) : Prop where
  cursor : (cur (ownerData W u) m).val=next
  stop : (m ((ownerData W u) 0+1).val).val=n
  directory : Recorded (ownerData W u) D m
  durable : ∀ a,keep a → m a=input a
  published : ∀ j : Fin n,j.val<next → picked D j.val=true → (v j).Cached id u j.val m

end ThreeFlat.RAM.HistoryStageBody.Physical

end OAI

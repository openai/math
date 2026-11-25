import OAI.ThreeFlat.Diagonal.TraceNodeLive
import OAI.ThreeFlat.Diagonal.TraceJournalRows
import OAI.ThreeFlat.Diagonal.TraceNodeCompactCode
import OAI.Hierarchy.TraceNodeSeedRows
import OAI.ThreeFlat.Diagonal.TraceNodePublishRun

namespace OAI
/-! # The compact physical S43/S44 publisher on a genuinely selected journal -/

namespace ThreeFlat.Diagonal.NavigationPass.NodePublication
open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.NavigationNodeRows RAM.PhysicalProcedure PhysicalStage
open NavigationDirectory TraceNodeHeaders
open scoped Fin.CommRing Classical
noncomputable section
variable {F : Type} [Field F] {W : ℕ}

/-- The completed native history retained every physical header word read by the compactor. -/
theorem compact_source_mounted {a : Archive} {limit s edges : ℕ} {cur ctr : Word W}
    (P : PhysicalStage.Program F s) (rem : ℕ) (X : State (2^s) (P.charge+rem))
    (bits : ℕ→Bool) (raw : List Bool) {input final : Memory W}
    (journal : a.TraceJournal limit cur ctr P rem X a.cursor raw input final)
    (visit : a.Visit (P.directory rem (Fintype.card X.Base)) edges bits cur [] X input)
    (seed : a.cursor.header=a.seed+64)
    (sep : (finish a.K (P.directory rem (Fintype.card X.Base)) a.cursor).header≤a.cursor.heap)
    (current : a.cursor.heap≤cur.val) (counter : cur.val<ctr.val) :
    MountedAt (natural final) a.K (P.directory rem (Fintype.card X.Base)) a.cursor := by
  apply MountedAt.of_splits
  intro pre op post steps j hj unchanged
  have v : a.Visit (pre++op::post) edges bits cur [] X input := steps ▸ visit
  have stop : (finish a.K (pre++op::post) a.cursor).header≤a.cursor.heap := steps ▸ sep
  have got:=TraceRecovery.field_mounted P rem X bits raw journal pre op post steps v seed stop
    current counter (⟨j,hj⟩:Fin 64) unchanged
  simpa only [natural,header_finish,Nat.add_assoc,Fin.val_mk] using got


end
end ThreeFlat.Diagonal.NavigationPass.NodePublication

end OAI

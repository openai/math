import OAI.Hierarchy.TaggedWideDatedRoleSheets

namespace OAI
/-! The first column of each native date table is the exact occupancy test for
the original signed state, also on roles never touched by a positive word. -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.DatedRoleSheets
open Computability.VPVNP.BurstRAM PrivateRAM WireTelescope AdaptiveProbe ProtocolRAM ReportSockets
open scoped Classical Fin.CommRing
variable {h W k attempts N native : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h)))
    (depth : ℕ) (marks : Marks h W k attempts) (unique : Exclusive marks) (rows : Fin N≃Source S π depth marks)
    (amount id : Fin N→ℕ) (capacity : Public S h W k attempts→ℕ)
    (fits : ∀i b,amount i≤capacity (named S π depth marks unique rows (i,b)))

theorem state_range (n start : ℕ) (memory : Memory native) (word : ∀i,amount i<2^native)
    (reported : roleFact n S π depth marks unique rows start amount id memory 0)
    (q : (r:Public S h W k attempts)×Fin (capacity r)) :
    q∈Set.range (statePlace S π depth marks unique rows amount capacity fits) ↔
      q.2.val<(memory (start+1+(shelfSlot S q.1).val)).val := by
  let port := named S π depth marks unique rows
  have width_data {I : Type} (size number peer : I → ℕ) :
      RoleField.width.data size number peer = size := by
    funext i
    rfl
  have stored (p : Public S h W k attempts) :
      memory (start+1+(shelfSlot S p).val)=
        (RoleWidths.shelf port (shelfSlot S) (fun z : Fin N×Bool=>amount z.1) (shelfSlot S p):Word native) := by
    simpa [sheet,sink,role,width_data,port] using reported (shelfSlot S p)
  apply NamedAperture.range_read _ amount port capacity fits
    (fun p => (memory (start+1+(shelfSlot S p).val)).val) _ _ q
  · intro i side
    rw [stored,RoleWidths.shelf_live]
    exact Fin.val_cast_of_lt (word i)
  · intro p none
    rw [stored,RoleWidths.shelf_blank _ _ _ _ none]
    rfl

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.DatedRoleSheets

end
end OAI

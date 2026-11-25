import OAI.Hierarchy.TaggedWideDatedRange

namespace OAI
/-! # Occupancy of a chronological width page after the remaining native phases -/
noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.DatedRoleSheets
open Computability.VPVNP.BurstRAM PrivateRAM WireTelescope AdaptiveProbe ProtocolRAM ReportSockets
open scoped Classical Fin.CommRing
variable {h W k attempts N native : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h)))
    (depth : ℕ) (marks : Marks h W k attempts) (unique : Exclusive marks)
    (rows : Fin N≃Source S π depth marks) (amount id : Fin N→ℕ)
    (capacity : Public S h W k attempts→ℕ)
    (fits : ∀i b,amount i≤capacity (named S π depth marks unique rows (i,b)))
include fits in
/-- The table is cleared even at roles without an originating paid row. -/
theorem roleFact.width_le (n start : ℕ) (memory : Memory native)
    (word : ∀i,amount i<2^native)
    (reported : roleFact n S π depth marks unique rows start amount id memory 0)
    (r : Public S h W k attempts) : (memory (start+1+(shelfSlot S r).val)).val≤capacity r := by
  let port := named S π depth marks unique rows
  have width_data {I : Type} (size number peer : I → ℕ) :
      RoleField.width.data size number peer = size := by
    funext i
    rfl
  have stored : memory (start+1+(shelfSlot S r).val)=
      (RoleWidths.shelf port (shelfSlot S) (fun z : Fin N×Bool=>amount z.1) (shelfSlot S r):Word native) := by
    simpa [sheet,sink,role,width_data,port] using reported (shelfSlot S r)
  rw [stored]
  by_cases live : r∈Set.range port
  · obtain ⟨⟨i,side⟩,rfl⟩:=live
    rw [RoleWidths.shelf_live,Fin.val_cast_of_lt (word i)]
    exact fits i side
  · rw [RoleWidths.shelf_blank _ _ _ _ live]
    exact Nat.zero_le _

/-- Later native phases can move or extend the work area. Observing the
original occupied-width cells suffices to recover the exact state-bit image. -/
theorem observed_range (n start : ℕ) (before after : Memory native)
    (word : ∀i,amount i<2^native)
    (reported : roleFact n S π depth marks unique rows start amount id before 0)
    (keep : ∀r : Public S h W k attempts,after (start+1+(shelfSlot S r).val)=before (start+1+(shelfSlot S r).val)) :
    (∀r : Public S h W k attempts,(after (start+1+(shelfSlot S r).val)).val≤capacity r) ∧
    (∀z:(r : Public S h W k attempts)×Fin (capacity r), z∈Set.range (statePlace S π depth marks unique rows amount capacity fits) ↔ z.2.val<(after (start+1+(shelfSlot S z.1).val)).val) := by
  constructor
  · intro r
    rw [keep]
    exact roleFact.width_le S π depth marks unique rows amount id capacity fits n start before word reported r
  · intro z
    rw [keep]
    exact state_range S π depth marks unique rows amount id capacity fits n start before word reported z

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.DatedRoleSheets

end
end OAI

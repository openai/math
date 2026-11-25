import OAI.Hierarchy.TaggedWideDatedRange
import OAI.Hierarchy.TaggedWideCalendarMiddle

namespace OAI
/-! The dense site-local bitmap reads all the allocated native degree slots,
including gaps in the public role enumeration. -/
noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.DatedRoleSheets
open Computability.VPVNP.BurstRAM PrivateRAM WireTelescope AdaptiveProbe ProtocolRAM ReportSockets
open scoped Classical Fin.CommRing
variable {h W k jobs N native : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h)))
    (depth : ℕ) (marks : Marks h W k jobs) (unique : Exclusive marks) (rows : Fin N≃Source S π depth marks)
    (amount id : Fin N→ℕ) (capacity : Public S h W k jobs→ℕ)
    (fits : ∀i b,amount i≤capacity (named S π depth marks unique rows (i,b)))
local notation "port" => named S π depth marks unique rows
local notation "socket" => shelfSlot S (h:=h) (W:=W) (k:=k) (attempts:=jobs)
local notation "sites" => siteLast h (2^W) k+1
local notation "deg" => stride k S.degree jobs

theorem dense_range (cap : ℕ) (within : ∀r,capacity r≤cap) (word : ∀i,amount i<2^native)
    (n start : ℕ) (memory : Memory native)
    (entry : roleFact n S π depth marks unique rows start amount id memory 0)
    (s : Fin sites) (x : Fin (deg*cap)) :
    (s,x)∈Set.range ((statePlace S π depth marks unique rows amount capacity fits).trans
        (LedgerStep.rolesChart capacity within socket)) ↔
      (finProdFinEquiv.symm x).2.val<(memory (start+1+(finProdFinEquiv (s,(finProdFinEquiv.symm x).1)).val)).val := by
  let q (se : Fin sites×Fin deg) := (memory (start+1+(finProdFinEquiv se).val)).val
  have width_data {I : Type} (size number peer : I → ℕ) :
      RoleField.width.data size number peer = size := by
    funext i
    rfl
  have stored (r : Fin (sites*deg)) :
      memory (start+1+r.val)=(RoleWidths.shelf port socket (fun i : Fin N×Bool=>amount i.1) r:Word native) := by
    simpa [sheet,sink,role,width_data] using entry r
  apply LedgerStep.rolesChart_occupied capacity within socket _ q _ _ _ s x
  · intro r
    change (memory (start+1+(finProdFinEquiv (finProdFinEquiv.symm (socket r))).val)).val≤capacity r
    rw [Equiv.apply_symm_apply,stored]
    by_cases found:r∈Set.range port
    · obtain ⟨i,rfl⟩:=found
      rw [RoleWidths.shelf_live,Fin.val_cast_of_lt (word i.1)]
      exact fits i.1 i.2
    · rw [RoleWidths.shelf_blank _ _ _ _ found]
      exact Nat.zero_le _
  · intro z none
    change (memory (start+1+(finProdFinEquiv z).val)).val=0
    rw [stored]
    have zero : RoleWidths.shelf port socket (fun i : Fin N×Bool=>amount i.1) (finProdFinEquiv z)=0 := by
      apply Function.extend_apply'
      rintro ⟨i,eq⟩
      exact none ⟨port i,eq⟩
    rw [zero]
    rfl
  · intro a
    simpa only [q,Equiv.apply_symm_apply] using
      state_range S π depth marks unique rows amount id capacity fits n start memory word entry a

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.DatedRoleSheets
end

end OAI

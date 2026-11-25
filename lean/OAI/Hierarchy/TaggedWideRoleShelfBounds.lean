import OAI.Hierarchy.TaggedWideDatedRoleSheets

namespace OAI
/-! # Native corrected widths at every numerical socket, including vacant ports -/
noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.DatedRoleSheets
open Computability.VPVNP.BurstRAM PrivateRAM WireTelescope AdaptiveProbe ProtocolRAM ReportSockets
open scoped Classical Fin.CommRing

variable {h W k jobs N native : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h)))
    (depth : ℕ) (marks : Marks h W k jobs) (unique : Exclusive marks) (rows : Fin N≃Source S π depth marks)
    (amount id : Fin N→ℕ)
local notation "port" => named S π depth marks unique rows
local notation "socket" => shelfSlot S (h:=h) (W:=W) (k:=k) (attempts:=jobs)
local notation "sites" => siteLast h (2^W) k+1
local notation "deg" => stride k S.degree jobs

theorem roleFact.socket_le (cap : ℕ) (bound : ∀i,amount i≤cap) (word : ∀i,amount i<2^native)
    (n start : ℕ) (m : Memory native) (printed : roleFact n S π depth marks unique rows start amount id m 0)
    (q : Fin (sites*deg)) : (m (start+1+q.val)).val≤cap := by
  have stored : m (start+1+q.val)=(RoleWidths.shelf port socket (fun z : Fin N×Bool=>amount z.1) q:Word native) := by
    have width_data (ids opposites : Fin N × Bool → ℕ) :
        RoleField.width.data (fun z : Fin N × Bool => amount z.1) ids opposites =
          (fun z : Fin N × Bool => amount z.1) := by
      funext z
      rfl
    simpa [sheet,sink,role,width_data] using printed q
  rw [stored]
  by_cases used : q∈Set.range (fun z : Fin N×Bool=>socket (port z))
  · obtain ⟨z,rfl⟩:=used
    rw [RoleWidths.shelf_live,Fin.val_cast_of_lt (word z.1)]
    exact bound z.1
  · have empty : RoleWidths.shelf port socket (fun z : Fin N×Bool=>amount z.1) q=0 := by
      exact Function.extend_apply' _ _ _ used
    rw [empty]
    exact Nat.zero_le _

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.DatedRoleSheets
end

end OAI

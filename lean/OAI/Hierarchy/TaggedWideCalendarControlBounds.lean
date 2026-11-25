import OAI.Hierarchy.TaggedWideCalendarSpillAddress
import OAI.Hierarchy.TaggedWideDatedROM

namespace OAI
/-! # Address bounds for the fixed chronological control and intermediate sheets -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.WideCPU.SpillDates
open WireTelescope.PassMatrix SiteControls
variable {T deg : ℕ} (z : SpillDates T) (start : ℕ)
local notation "P" => z.original
local notation "r" => z.roleRoot start 2

private theorem control_interior (j : Fin T) (s : Fin (P).sites) (f : SiteControls.Field deg)
    (columns : (P).controlColumns j=SiteControls.fieldCount deg) :
    1+s.val*(P).controlColumns j+(fieldNumber deg f).val<((P).control j).span (P).sites := by
  have field : (fieldNumber deg f).val<(P).controlColumns j :=
    lt_of_lt_of_eq (fieldNumber deg f).isLt columns.symm
  have toNext:=Nat.add_lt_add_left field (s.val*(P).controlColumns j)
  have fits:=Nat.mul_le_mul_right ((P).controlColumns j) s.isLt
  rw [Nat.succ_mul] at fits
  change _<1+(P).sites*(P).controlColumns j+2*((P).control j).count
  omega

/-- Every requested word is strictly inside the common end of the two
original control sheets, including the sentinel ballot of a spill date. -/
theorem calendar_control_addresses (j : Fin T) (s : Fin (P).sites)
    (columns : (P).controlColumns j=SiteControls.fieldCount deg) :
    (∀ f : SiteControls.Field deg,controlAddress P (z.spillControlWork start) j s f<z.endAt start) ∧
    (∀ f : SiteControls.Field deg,controlAddress P r j s f<z.endAt start) ∧
    ballotAddress P r j s 0<z.endAt start := by
  have first:=extent ((P).controlStart r) (fun i=>((P).control i).span (P).sites) j
  change (P).controlBase r j+((P).control j).span (P).sites≤ (P).maskStart r at first
  have second:=extent ((P).maskStart r) (fun i=>((P).control i).span (P).sites) j
  change z.spillStart start j+((P).control j).span (P).sites≤ z.endAt start at second
  have top : (P).maskStart r≤ z.endAt start:=Nat.le_add_right ..
  refine ⟨?_,?_,?_⟩
  · intro f
    rw [z.spillControlAddress]
    have low:=control_interior z j s f columns
    omega
  · intro f
    unfold controlAddress
    have low:=control_interior z j s f columns
    omega
  · have left:=extent ((P).rolesEnd r) (fun i=>((P).ballot i).span (P).sites) j
    change (P).ballotStart r j+((P).ballot j).span (P).sites≤ (P).controlStart r at left
    have small:=Nat.mul_le_mul_right ((P).ballot j).columns s.isLt.le
    have pos : 0<((P).control j).span (P).sites:=by unfold Shape.span; omega
    have below : (P).controlStart r≤ (P).controlBase r j:=Nat.le_add_right ..
    dsimp only [ballotAddress,Shape.span] at left ⊢
    omega

/-- The entire original native ballot row is interior to its own span. -/
theorem calendar_ballot_address (j : Fin T) (s : Fin (P).sites) (f : Fin ((P).ballot j).columns) :
    ballotAddress P r j s f.val<z.endAt start := by
  have slab:=extent ((P).rolesEnd r) (fun i=>((P).ballot i).span (P).sites) j
  change (P).ballotStart r j+((P).ballot j).span (P).sites≤ (P).controlStart r at slab
  have frow:=Nat.add_lt_add_left f.isLt (s.val*((P).ballot j).columns)
  have width:=Nat.mul_le_mul_right ((P).ballot j).columns s.isLt
  rw [Nat.succ_mul] at width
  have controls : (P).controlStart r≤ (P).maskStart r:=Nat.le_add_right ..
  have last : (P).maskStart r≤ z.endAt start:=Nat.le_add_right ..
  dsimp only [ballotAddress,Shape.span] at slab ⊢
  omega

/-- The middle guard is the first role-word sheet of the actual post-date
bank, at its original site and neighbor ordinal. -/
theorem calendar_middle_address (j : Fin T) (i : Fin (P).roleWords) :
    ProbeStage.CoreBoard.HistoryRoles.DatedRoleSheets.sheet (z.dateRole start j 0)
      (P).roleWords (P).physical 0+i.val<z.endAt start := by
  let root:=z.roleRoot start 0
  have block : 1+i.val<3*(P).roleSpan:=by
    unfold Dated.roleSpan ProbeStage.CoreBoard.HistoryRoles.DatedRoleSheets.span
    have inside:=i.isLt
    omega
  have after:=Nat.mul_le_mul_right (3*(P).roleSpan) (show j.succ.val+1≤ T+1 from j.succ.isLt)
  rw [Nat.add_mul,Nat.one_mul] at after
  have first : (P).roleStart root j.succ+1+i.val<(P).rolesEnd root:=by
    dsimp only [Dated.roleStart,Dated.rolesEnd]
    omega
  have roots : root≤ r:=by simp [root,SpillDates.roleRoot]
  have order : (P).rolesEnd root≤ (P).rolesEnd r:=Nat.add_le_add_right roots _
  have ballot : (P).rolesEnd r≤ (P).controlStart r:=Nat.le_add_right ..
  have controls : (P).controlStart r≤ (P).maskStart r:=Nat.le_add_right ..
  have last : (P).maskStart r≤ z.endAt start:=Nat.le_add_right ..
  simpa only [ProbeStage.CoreBoard.HistoryRoles.DatedRoleSheets.sheet,
    ProbeStage.CoreBoard.HistoryRoles.DatedRoleSheets.sink,Fin.val_zero,Nat.zero_mul,Nat.add_zero,
    SpillDates.dateRole,root] using first.trans_le (order.trans (ballot.trans (controls.trans last)))

end Hierarchy.ProtocolRAM.Calendar.WideCPU.SpillDates
end

end OAI

import OAI.Hierarchy.DescentPhysicalMixedSectors
import OAI.Hierarchy.DescentCalendarMixedGeometry

namespace OAI
/-! # Row-major mixed job addresses for the two non-stem candidate sectors -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs.SheetGeometry
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {a : PhysicalReset} {floor w : ℕ} {u : a.DateInputs floor w} (s : SheetGeometry u)
local notation "v₀" => a.successor
local notation "s₀" => (v₀).sheets
local notation "step₀" => (s₀).contacts+(s₀).privates

private theorem parts {x r n : ℕ} (hit : r<n) : (x*n+r)/n=x ∧ (x*n+r)%n=r := by
  have pos:=Nat.zero_lt_of_lt hit
  constructor
  · rw [Nat.mul_comm x n,Nat.mul_add_div pos,Nat.div_eq_of_lt hit,Nat.add_zero]
  · rw [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt hit]

theorem contact_job (x : Fin (s₀).blocks) (t : Fin (s₀).contacts) :
    (v₀).jobAt (x.val*step₀+t.val)=some (.inl (x.cast s.contactBlocks,t.cast s.contacts)) :=by
  have hit : t.val<step₀:=t.isLt.trans_le (Nat.le_add_right ..)
  obtain ⟨quot,rem⟩:=parts (x:=x.val) hit
  have left : x.val<(v₀).contactShape.blocks ∧ t.val<(v₀).contactShape.sockets:=
    ⟨s.contactBlocks ▸ x.isLt,s.contacts ▸ t.isLt⟩
  unfold ResetOutput.jobAt
  have sum : (v₀).contactShape.sockets+(v₀).privateShape.keys=step₀:=congrArg₂ Nat.add s.contacts.symm s.privates.symm
  simp only [sum,quot,rem,dite_eq_left left]
  rfl

theorem private_job (x : Fin (s₀).blocks) (t : Fin (s₀).privates) :
    (v₀).jobAt (x.val*step₀+((s₀).contacts+t.val))=some (.inr (x.cast s.privateBlocks,t.cast s.privates)) :=by
  have hit : (s₀).contacts+t.val<step₀:=Nat.add_lt_add_left t.isLt _
  obtain ⟨quot,rem⟩:=parts (x:=x.val) hit
  have sum : (v₀).contactShape.sockets+(v₀).privateShape.keys=step₀:=congrArg₂ Nat.add s.contacts.symm s.privates.symm
  have first : ¬(x.val<(v₀).contactShape.blocks ∧ (s₀).contacts+t.val<(v₀).contactShape.sockets):=by rw [←s.contacts]; omega
  have sub : (s₀).contacts+t.val-(v₀).contactShape.sockets=t.val:=by rw [←s.contacts]; omega
  have second : x.val<(v₀).privateShape.blocks ∧ (v₀).contactShape.sockets≤(s₀).contacts+t.val ∧ t.val<(v₀).privateShape.keys:=
    ⟨s.privateBlocks ▸ x.isLt,by rw [←s.contacts];exact Nat.le_add_right _ _,s.privates ▸ t.isLt⟩
  unfold ResetOutput.jobAt
  simp only [sum,quot,rem,dite_eq_right first,sub,dite_eq_left second]
  rfl

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs.SheetGeometry

end OAI

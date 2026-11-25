import OAI.Hierarchy.DescentPhysicalResetDate

namespace OAI
/-! # Retained role, class, venue and old root registers at the primitive-role instruction -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.FinalInputs
open DescentSixParty DescentSixParty.Chronology ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
variable {a : PhysicalReset} {floor w : ℕ} {u : a.DateInputs floor w} (z : FinalInputs u)
local notation "v" => a.successor
local notation "b" => a.rebased floor
local notation "ds" => (v).actor.directory ((v).middle.stop b)
local notation "P₀" => a.stencilPhase u.shape floor u.count u.hub u.g u.Y
local notation "key" => (⟨(P₀).saved,0⟩ : Bank)
local notation "roleAt" => (v).fullEnd b
local notation "movedAt" => (v).roleEnd b
local notation "classAt" => (v).classEnd b
local notation "bornAt" => (v).birthEnd b
local notation "meta" => (v).primitiveEnd b

/-- The predecessor cutoffs use the actual semantic RAM images instead of
retrospectively observing scratch through the completed date. -/
theorem role_input_frames (fit : z.Room) (mid : Memory w) :
    (∀x,x<classAt ∨ bornAt≤x→z.roleInput mid x=z.classImage mid x) ∧
    (∀x,x< movedAt ∨ bornAt≤x→z.roleInput mid x=z.retainedImage mid x) ∧
    ∀x,x<roleAt ∨ bornAt≤x→z.roleInput mid x=z.venueImage mid x :=by
  have start_ : roleAt≤ movedAt:=by rw [ResetOutput.roleEnd,(v).roleTransfer.translate];exact Nat.le_add_right ..
  have class_ : movedAt≤classAt:=((v).actorClass.guard movedAt).1.trans ((v).actorClass.guard movedAt).2
  have born_ : classAt≤bornAt:=by rw [ResetOutput.birthEnd,(v).birth.translate];exact Nat.le_add_right ..
  have prim_ : bornAt≤ meta:=by rw [ResetOutput.primitiveEnd,(v).primitive.translate];exact Nat.le_add_right ..
  have top_ : meta≤a.endAddress floor:=by
    change _≤(v).metadata.endAddress meta
    rw [(v).metadata.translate];exact Nat.le_add_right ..
  have r:=(v).roleTransfer.any roleAt z.previousRoles key (ds).count (ds).inverse z.which (oldMatrix u) (z.venueImage mid) fit.roleMove
  have c:=(v).actorClass.any movedAt z.classKey (z.retainedImage mid)
    (born_.trans_lt (prim_.trans_lt (top_.trans_lt fit.endFits)))
  have h:=(v).birth.any classAt z.guards (ds).count (ds).inverse (z.classImage mid) fit.birth
    (prim_.trans_lt (top_.trans_lt fit.endFits))
  have retained (x : ℕ) (outside:x< movedAt ∨ bornAt≤x) : z.roleInput mid x=z.retainedImage mid x :=
    (h.2.2 x (outside.imp_left (·.trans_le class_))).trans (c.2.2 x (outside.imp_right (born_.trans ·)))
  exact ⟨h.2.2,retained,fun x outside=>(retained x (outside.imp_left (·.trans_le start_))).trans
    (r.2.2 x (outside.imp_right ((class_.trans born_).trans ·)))⟩

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.FinalInputs

end OAI

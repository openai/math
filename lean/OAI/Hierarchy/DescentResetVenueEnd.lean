import OAI.Hierarchy.DescentDatedResetOutput

namespace OAI
namespace Hierarchy.DescentDatedAddressBook.ResetOutput

theorem venue_before_metadata (v : ResetOutput) (b : ℕ) : v.fullEnd b≤v.metadataEnd b:=by
  have move_ : v.fullEnd b≤v.roleEnd b:=by rw [roleEnd,v.roleTransfer.translate];exact Nat.le_add_right ..
  have classes : v.roleEnd b≤v.classEnd b:=by rw [classEnd,v.actorClass.translate];exact Nat.le_add_right ..
  have birth : v.classEnd b≤v.birthEnd b:=by rw [birthEnd,v.birth.translate];exact Nat.le_add_right ..
  have token : v.birthEnd b≤v.primitiveEnd b:=by rw [primitiveEnd,v.primitive.translate];exact Nat.le_add_right ..
  have book : v.primitiveEnd b≤v.metadataEnd b:=by rw [metadataEnd,v.metadata.translate];exact Nat.le_add_right ..
  exact move_.trans (classes.trans (birth.trans (token.trans book)))

end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI

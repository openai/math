import OAI.Hierarchy.DescentSignedStageFormat

namespace OAI
/-! # Width of each real selector read in an ordinary material row -/
namespace Hierarchy.DescentDatedAddressBook.SignedStage
theorem fieldBits_le_unit (q : SignedStage) : q.fieldBits ≤ q.unit :=
  (Nat.le_add_left q.fieldBits (q.fieldBits*2^q.k)).trans (le_max_right ..)
end Hierarchy.DescentDatedAddressBook.SignedStage

end OAI

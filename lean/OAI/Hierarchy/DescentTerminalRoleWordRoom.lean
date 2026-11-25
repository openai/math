import OAI.Hierarchy.DescentTerminalRoleWords

namespace OAI
/-! The earned bit width of the six physical input shelves. -/
namespace Hierarchy.DescentSixParty
open scoped BigOperators
/-- The input data of the actual six physical shelves has exactly the calendar bit total. -/
theorem role_words_room (n a g p stride nodes groups h:ℕ)
    (paid:32*(groups*(DescentBundleTagKeys.width (Nat.clog 2 (n+1)) a g p stride*nodes+1))≤h)
    (pos:0<groups) :
    (∑f:Fin 6,DescentTerminalCombinedRole.width n a g p stride f*nodes*groups)+3≤h/2 := by
  rw [DescentTerminalCombinedRole.payload_size]
  change DescentBundleTagKeys.width (Nat.clog 2 (n+1)) a g p stride*nodes*groups+3≤h/2
  rw [Nat.mul_add,Nat.mul_one] at paid
  rw [Nat.mul_comm (_*nodes) groups]
  omega

end Hierarchy.DescentSixParty

end OAI

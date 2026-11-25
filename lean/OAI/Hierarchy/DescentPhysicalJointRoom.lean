import OAI.Hierarchy.DescentPhysicalResetDateOperands

namespace OAI
/-! # Address room from the allocated compact actor and sparse peer rows -/
namespace Hierarchy.DescentDatedAddressBook
open DescentDyadicSpan DescentResetPeerJointRAM DescentSIMDLookup
noncomputable section

theorem ResetOutput.joint_hosts (v : ResetOutput) (base : ℕ) :
    v.sheets.hosts≤v.jointEnd base ∧ v.front.peer.hosts≤v.jointEnd base :=by
  have sparse:=span_ge v.front.peer.hosts
  have compact:=span_ge v.sheets.hosts
  have bounds (a b c d : ℕ) :
      v.sheets.hosts ≤ v.massEnd base + 3*span v.front.peer.hosts + 4*v.sheets.hosts +
        span v.sheets.hosts + a + b + c + d ∧
      v.front.peer.hosts ≤ v.massEnd base + 3*span v.front.peer.hosts + 4*v.sheets.hosts +
        span v.sheets.hosts + a + b + c + d := by
    constructor <;> omega
  exact bounds _ _ _ _

theorem PhysicalReset.DateInputs.joints_of_roof {a : PhysicalReset} {floor w : ℕ}
    (u : a.DateInputs floor w)
    (palette : 0<a.successor.front.peer.shapes)
    (roof : a.successor.jointEnd (a.rebased floor)<2^w) :
    a.successor.JointRoom (a.rebased floor) u.earlier w :=by
  have count:=a.successor.joint_hosts (a.rebased floor)
  have old : a.successor.front.peer.oldHosts≤a.successor.front.peer.hosts:=by
    change _≤a.successor.front.peer.oldHosts*a.successor.front.peer.shapes
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left a.successor.front.peer.oldHosts palette
  exact a.successor.joint_room (a.rebased floor) u.earlier u.sceneFits
    ((old.trans count.2).trans_lt roof) (count.1.trans_lt roof) roof

end
end Hierarchy.DescentDatedAddressBook

end OAI

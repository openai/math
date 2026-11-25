import OAI.Hierarchy.DescentPreviousOperandLayout

namespace OAI
/-! The rounded final row of every earlier operand bank fits in its published rectangle. -/
namespace Hierarchy.DescentDatedPriorOperand
open DescentOperandStateBanks ProtocolRAM
namespace Layout

def previousLimit (l : Layout) (base : ℕ) :=
  base+(7*l.operands)*(l.blocks*l.rows)+2^Nat.clog 2 (l.rows+1)

theorem previous_fit (l : Layout) (base cut w : ℕ) (done : l.previousLimit base≤cut)
    (room : cut<2^w) (x : Fin l.blocks) (p : Pages l.operands) :
    (previousBank l base x p).Fits w cut :=by
  have lo : p.val*(l.blocks*l.rows)+x.val*l.rows≤(7*l.operands)*(l.blocks*l.rows):=calc
    _ ≤ p.val*(l.blocks*l.rows)+l.blocks*l.rows:=
      Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_of_lt x.isLt)) _
    _ = (p.val+1)*(l.blocks*l.rows):=(Nat.succ_mul ..).symm
    _ ≤ _:=Nat.mul_le_mul_right _ p.isLt
  have placed : (previousBank l base x p).base+(previousBank l base x p).size≤cut:=by
    apply le_trans _ done
    simpa only [previousBank,previousLimit,Bank.size,Nat.add_assoc] using
      Nat.add_le_add_right (Nat.add_le_add_left lo base) (2^Nat.clog 2 (l.rows+1))
  exact ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (placed.trans_lt room),placed⟩

end Layout
end Hierarchy.DescentDatedPriorOperand

end OAI

import OAI.Hierarchy.DescentDatedPriorOperand
import OAI.Hierarchy.DescentOperandStateBanks

namespace OAI
/-! # Address of a prior operand page indexed by physical block -/
namespace Hierarchy.DescentDatedPriorOperand
open DescentOperandStateBanks ProtocolRAM
/-- The exact directory entry used by the previous all-properties transpose. -/
def previousBank (l : Layout) (base : ℕ) (block : Fin l.blocks) (p : Pages l.operands) : Bank:=
  ⟨base+p.val*(l.blocks*l.rows)+block.val*l.rows,Nat.clog 2 (l.rows+1)⟩

end Hierarchy.DescentDatedPriorOperand

end OAI

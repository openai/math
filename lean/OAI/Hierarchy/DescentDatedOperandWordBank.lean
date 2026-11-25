import OAI.Hierarchy.DescentDatedPriorOperand

namespace OAI
/-! The physical packed output bank of an ordinary resolver job. -/
namespace Hierarchy.DescentDatedPriorOperand.Banks
open DescentSIMDLookup ProtocolRAM

abbrev wordBank (l : Layout) (floor : ℕ) (j : Fin l.jobs) : Bank :=
  ⟨l.output (l.slot floor j.val),Nat.clog 2 (l.rows+1)⟩

end Hierarchy.DescentDatedPriorOperand.Banks

end OAI

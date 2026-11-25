import OAI.Hierarchy.DescentDatedPriorOperand
import OAI.Hierarchy.DescentOperandStateBanks

namespace OAI
/-! Physical banks used for every dated job in the original operand program. -/
namespace Hierarchy.DescentDatedPriorOperand
open DescentOperandStateBanks ProtocolRAM
noncomputable section

/-- The archive addresses, six installed selector inputs and the new signed
endpoint, old outgoing address and original party-role columns. All of these
are addresses from the public allocation, independent of loaded row values. -/
structure Banks (l : Layout) where
  previous : Fin l.blocks→Pages l.operands→Bank
  side : Fin l.jobs→Fin 6→Bank
  route : Fin l.jobs→Fin 3→Bank

namespace Banks
variable {l : Layout} (t : Banks l)

def book (j : Fin l.jobs) :=t.previous ((l.index).symm j).1

structure Early (t : Banks l) (floor w : ℕ) : Prop where
  previous : ∀j p,(t.book j p).Fits w floor ∧ l.rows≤(t.book j p).size
  side : ∀j i,(t.side j i).Fits w floor ∧ l.rows≤(t.side j i).size
  route : ∀j i,(t.route j i).Fits w floor ∧ l.rows≤(t.route j i).size

end Banks
end
end Hierarchy.DescentDatedPriorOperand

end OAI

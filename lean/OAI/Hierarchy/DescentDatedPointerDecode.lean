import OAI.Hierarchy.DescentTicketFragment

namespace OAI
/-! # Reading the prior pointer from its four stored scalar fields -/
namespace Hierarchy.DescentDatedPriorOperand
open DescentSIMDLookup DescentOperandStateBanks
open scoped Classical Fin.CommRing
noncomputable section
def decodeHeader {s : ℕ} (v : Fin 4→Cell s) : Pointer :=
  if (v 0).val=1 then .cable (v 1).val (v 2).val (v 3).val
  else if (v 0).val=2 then .pin (v 2).val (v 3).val else .privateWord (v 2).val

theorem decode_of_pointer {s : ℕ} {v : Fin 4→Cell s} {p : Pointer} (issued : ∀i,(v i).val=p.header i) :
    decodeHeader v=p:=by cases p <;> simp [decodeHeader,issued,Pointer.header]

end
end Hierarchy.DescentDatedPriorOperand

end OAI

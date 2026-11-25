import OAI.Hierarchy.DescentDatedOperandDigits
import OAI.Hierarchy.DescentRegisteredOperandFields
import OAI.Hierarchy.DescentTicketFragment

namespace OAI
/-! # The independently read side fields of a registered ordinary operand -/
namespace Hierarchy.DescentPriorOperandColumns
open DescentSIMDLookup DescentPackedOperand DescentOperandStateBanks
open DescentRawCablePanel.DepotRAM.Operand ProtocolRAM
noncomputable section
variable {k : ℕ}

/-- Physical side data in the public order used by the ten-field resolver. -/
def Side.digits (s : Side k) : Fin 6→Cell (k+2) :=
  ![s.donor,flagCell k s.firstCapture,flagCell k s.secondCapture,flagCell k s.marked,s.start,s.grain]

theorem Side.side_value (s : Side k) (p : Pointer) (fit : ∀f,p.header f<2^(k+2)) (i : Fin 6) :
    sourceFields (s.withHeader p fit) (sideIndex i)=s.digits i := by
  cases p <;> fin_cases i <;> rfl

end
end Hierarchy.DescentPriorOperandColumns

end OAI

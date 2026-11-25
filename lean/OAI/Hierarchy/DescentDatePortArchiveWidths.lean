import OAI.Hierarchy.DescentRegisterTypes
import OAI.Hierarchy.DescentPrimitivePalettePrintedBits
import OAI.Hierarchy.DescentResetRetainedCalendarWidths

namespace OAI
/-! # Widths of the operand and primitive banks retained at a date -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentCompiler DescentPrimitivePalette
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F) (S : AtomSchedule) (op : RotorSpec)

structure ArchiveWidths (ports : DatePorts) (k tail p drift degree h age : ℕ) : Prop where
  nodes : ports.nodes=if age=0 then 1 else S.retainedNodes
  digits : ports.operandBits=DescentOperandWidth.recordBits G S k tail drift degree p
  token : ports.tokenBits=printedBits G (S.firstWidth G.b p) (S.grainAt G.b p 0) op
  operands : ports.operandBits*ports.nodes*ports.operandLanes≤h/2
  roles : printedBits G (S.firstWidth G.b p) (S.grainAt G.b p 0) op*ports.nodes*ports.roleLanes≤h/2

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI

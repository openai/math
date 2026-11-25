import OAI.Hierarchy.DescentDatedOperandNativePreparation
import OAI.Hierarchy.DescentDatedReadPipelineFee
import OAI.Hierarchy.DescentDatedWOriginPrice

namespace OAI
/-! # Native expression work after resampling the dated operand source words -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedOperandReadPipeline ProtocolRAM
noncomputable section
variable {F Pin : Type} [Field F] (v : PhysicalOrdinary F Pin)

theorem native_ticket_work (floor : ℕ) (c : v.SignedChart) (A : v.ArgumentEntry) (mat : A.Match v floor)
    (shape : v.VectorShape) (blocks : v.resolver.blocks=v.material.blocks) :
    Sources.Work v.ticketReadGeometry (v.nativeTicketSources floor c A mat shape blocks) 32 :=by
  constructor
  · intro j f
    exact v.originPort_work floor v.operandShortBits _ _ f
  · intro j f
    change 17≤32
    decide
  · intro j f
    change 17≤32
    decide
  · intro j f i
    change 12≤32
    decide
  · intro i
    change 12≤32
    decide
  · intro j f i
    change 12≤32
    decide
  · intro j f i
    change 12≤32
    decide
  · intro i
    change 12≤32
    decide

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI

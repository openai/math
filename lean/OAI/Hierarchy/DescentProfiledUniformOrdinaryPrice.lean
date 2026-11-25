import OAI.Hierarchy.DescentProfiledOrdinaryUniformSpan
import OAI.Hierarchy.DescentUniformOperandRoofs
import OAI.Hierarchy.DescentProfiledUniformReference

namespace OAI
/-! A common exponent for the actual public ordinary pointer and signed tests
before the calendar skew and word parameters are chosen. -/
namespace Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer
open Chronology DescentDatedAddressBook Filter
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ}
    (board : NonlinearExpanders.Graph n d) (op : RotorSpec) (t f g reset drift bound : ℕ)

theorem uniform_ordinary_spans : UniformRoof G board op t f g reset drift bound
    (fun _ _ _ x=>max x.endAt (x.model.signedGuard x.stageFloor)-x.slot.position.floor) :=by
  obtain ⟨R,ref⟩:=uniform_reference G board op t f g reset drift bound
  exact uniform_span_from_operands G board op t f g reset drift bound
    (uniform_operand_roofs G board op t f g reset drift bound) ⟨R,fun τ B _ slack _=>ref τ B slack⟩

end Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer

end OAI

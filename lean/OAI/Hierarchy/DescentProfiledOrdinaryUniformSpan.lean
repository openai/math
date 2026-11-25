import OAI.Hierarchy.DescentProfiledUniformCeilingSum
import OAI.Hierarchy.DescentProfiledUniformSurvivor
import OAI.Hierarchy.DescentProfiledOrdinaryUniformVenue
import OAI.Hierarchy.DescentProfiledOrdinaryUniformPrimitive

namespace OAI
namespace Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer
open DescentCompiler DescentCompiler.TerminalScale Chronology Filter
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)
  (op : RotorSpec) (t f g reset drift bound : ℕ)
local notation "budget" => UniformRoof G board op t f g reset drift bound

theorem uniform_span_from_operands
    (parts : budget (fun _ _ _ x=>x.model.vector.endAddress 0+x.model.resolver.endAddress 0+
      x.model.metadata.ordinaryEnd 0+x.model.operandBook.endAddress 0))
    (reference : budget (fun _ _ _ x=>x.model.referenceWords)) :
    budget (fun _ _ _ x=>max x.endAt (x.model.signedGuard x.stageFloor)-x.slot.position.floor) :=by
  obtain ⟨S,ret⟩:=uniform_survivor G board op t f g reset drift bound
  obtain ⟨V,venue⟩:=uniform_final_venue G board op t f g reset drift bound
  obtain ⟨P,prim⟩:=uniform_primitive G board op t f g reset drift bound
  apply uniform_span_sum G board op t f g reset drift bound parts
    ⟨S,fun τ B _ slack _=>ret τ B slack⟩ reference
  · exact ⟨V,fun τ B _ small short=>(venue τ B small short).mono
      fun h vals x=>by simpa only [←pow_mul,Nat.mul_comm h V] using vals x⟩
  · exact ⟨P,fun τ B den _ _=>prim τ B den⟩

end
end Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer

end OAI

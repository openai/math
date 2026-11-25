import OAI.Hierarchy.DescentProfiledOrdinarySignedGuard
import OAI.Hierarchy.DescentRegisteredSignedBeforeFull

namespace OAI
/-! # The signed program's public address limit on the selected ordinary offers -/
namespace Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer
open DescentCompiler DescentCompiler.TerminalScale DescentInitialHost Chronology
open DescentDatedAddressBook DescentResetInvoice
open ThreeFlat.Routing
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ}
    (board : NonlinearExpanders.Graph n d) (op : RotorSpec) (t f g reset τ drift degreeMax B : ℕ)
set_option quotPrecheck false
local notation "idx" h:arg => ProfiledOrdinaryOffer G f g board op t reset τ drift degreeMax B h

theorem signed_guard_of_ceiling
    (allocated : Bounded (fun h (x : idx h)=>x.model.fullCeiling)) :
    Bounded (fun h (x : idx h)=> x.model.signedGuard x.stageFloor-x.slot.position.floor) := by
  apply (allocated.add (signed_guard_excess G board op t f g reset τ drift degreeMax B)).of_le
  intro h x
  simpa only [x.model_floor] using x.model.signed_guard_span x.slot.position.floor

/-- A single address exponent fits both the returned end and the signed program's guard. -/
theorem guarded_span_of_ceiling
    (allocated : Bounded (fun h (x : idx h)=>x.model.fullCeiling)) :
    Bounded (fun h (x : idx h)=>max x.endAt (x.model.signedGuard x.stageFloor)-x.slot.position.floor) :=by
  have returned : Bounded (fun h (x : idx h)=>x.endAt-x.slot.position.floor) :=
    allocated.of_le fun _ x=>x.span_le
  apply (returned.max' (signed_guard_of_ceiling G board op t f g reset τ drift degreeMax B allocated)).of_le
  intro h x
  omega

end
end Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer

end OAI

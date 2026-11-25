import OAI.Hierarchy.DescentDatedSignedInput
import OAI.Hierarchy.DescentSelectedSignedBill

namespace OAI
/-! # The issued dimensions address all four dependent socket indices -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentCompiler DescentCompiler.TerminalScale DescentDatedAddressBook DescentRawCablePanel DescentStaticWordColumn
noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P)

theorem issuedSignedChart : v.withIssuedSigned.SignedChart where
  degree:=rfl
  blocks:=rfl
  seats:=by change 2^v.k*v.prior.placement.cap*11=2^v.k*(v.prior.placement.cap*11);exact Nat.mul_assoc ..
  markSlots:=rfl

/-- Internalize the true socket query prices and the actual marked bank base. -/
theorem selected_signed_phase {t f g reset J M tail : ℕ}
    (calendar : v.schedule=stageNumbers v.gadget t J f g reset M tail)
    (radix : v.k=groupBits t J (hostRate t reset) (capRate v.gadget t g) (cutRate t f g))
    (floor w ratio : ℕ) (degree : v.venue.degree=v.target.placement.degree)
    (fieldRoom : 2*scale J (signedRates v.gadget t f g reset).amount≤v.payload)
    (machine : w≤ratio*v.payload) :
    let rate:=signedRates v.gadget t f g reset
    let native:=v.withIssuedSigned.signedPhase floor v.issuedSignedChart w
    (native.ticks+7*names native.program)*w≤ratio*scale J rate.controls*
      ((1+2^(v.payload/2)+2*(v.area.H+v.venue.hosts))*v.payload+
        4*(v.area.H+v.venue.hosts)*v.schedule.groupCount (v.age+1)*scale J rate.amount) := by
  have work:=v.withIssuedSigned.signed_work floor v.issuedSignedChart
  change v.withIssuedSigned.signed.SnippetWork _ (max v.venue.degree 88) at work
  rw [degree] at work
  exact v.selected_signed_bill calendar radix _ floor w ratio work fieldRoom machine

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI

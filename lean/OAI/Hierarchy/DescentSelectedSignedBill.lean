import OAI.Hierarchy.DescentSelectedSignedRates
import OAI.Hierarchy.DescentPhysicalSignedFormat

namespace OAI
/-! # Charge the native signed successor to the two real host populations -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentCompiler DescentCompiler.TerminalScale DescentDatedAddressBook DescentStaticWordColumn
noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P)

/-- The shape comes from the issued transition. Only the actual expression bound
for its seven input snippets is needed from the preceding materialization. -/
theorem selected_signed_bill {t f g reset J M tail : ℕ}
    (calendar : v.schedule=stageNumbers v.gadget t J f g reset M tail)
    (radix : v.k=groupBits t J (hostRate t reset) (capRate v.gadget t g) (cutRate t f g))
    (I : v.withIssuedSigned.signed.Input) (floor w ratio : ℕ)
    (snippets : v.withIssuedSigned.signed.SnippetWork I (max v.target.placement.degree 88))
    (fieldRoom : 2*scale J (signedRates v.gadget t f g reset).amount≤v.payload)
    (machine : w≤ratio*v.payload) :
    let rate:=signedRates v.gadget t f g reset
    let s:=v.withIssuedSigned.signed
    let start:=v.withIssuedSigned.markEnd floor
    (s.phaseTicks I start w+7*names (s.phase I start w).program)*w ≤
      ratio*scale J rate.controls*
        ((1+2^(v.payload/2)+2*(v.area.H+v.venue.hosts))*v.payload+
          4*(v.area.H+v.venue.hosts)*v.schedule.groupCount (v.age+1)*scale J rate.amount) := by
  have row:=v.ticket.selected_signed_rates calendar radix v.area.H v.venue.hosts
    (v.schedule.groupCount (v.age+1)) v.payload
  let r:=signedRates v.gadget t f g reset
  have width : v.signedLayout.unit ≤ scale J r.amount:=row.1
  have controls : v.withIssuedSigned.signed.feedFactor (max v.target.placement.degree 88) ≤ scale J r.controls:=row.2
  have room:2*v.signedLayout.unit≤v.payload:=(Nat.mul_le_mul_left 2 width).trans fieldRoom
  have run:=v.issued_feed_mark_bill I floor w (max v.target.placement.degree 88) ratio snippets room machine
  refine run.trans (Nat.mul_le_mul (Nat.mul_le_mul_left ratio controls) ?_)
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ width) _

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI

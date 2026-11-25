import OAI.Hierarchy.DescentNamedOrdinaryVenue
import OAI.Hierarchy.DescentFundedClipChoice
import OAI.Hierarchy.DescentPhysicalSignedFormat

namespace OAI
/-! # The clipped and signed ordinary constructors retain the same actual venue -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentCompiler DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage.Dated
noncomputable section
variable {F P:Type} [Field F] (v:PhysicalOrdinary F P)

theorem venue_after_clip (gain frozen p f priorM extra:ℕ)(orig:ℕ→Ordinary)
    (date:v.venue=StageVenueTail.Date.atOrdinary v.gadget v.schedule gain v.k frozen p f v.payload orig v.age priorM)
    (format:v.signedLayout=SignedStage.atDate v.gadget v.schedule gain v.k v.age (NativePitch.incomingHosts v.schedule (v.age+1))):
    let u:=v.withIssuedSigned
    let w:=u.withFundedClip extra
    w.venue=StageVenueTail.Date.atOrdinary v.gadget v.schedule gain v.k frozen p f v.payload orig v.age
        (u.fundedClip extra).postPitch ∧
      w.venue.signedLanes=w.signed.lanes ∧ w.venue.paidBits=v.schedule.censusBits p ∧
      w.venue.hosts=NativePitch.incomingHosts v.schedule (v.age+1) ∧
      w.venue.lanes=NativePitch.incoming v.schedule v.k frozen p f v.payload orig (v.age+1):=by
  intro u w
  have changed:w.venue={v.venue with paidLanes:=(u.fundedClip extra).postPitch,aliveLanes:=(u.fundedClip extra).postPitch}:=rfl
  rw [changed,date]
  refine ⟨rfl,?_,rfl,rfl,rfl⟩
  change (SignedStage.signedAt v.gadget v.schedule gain v.k v.age v.payload).lanes=
    (v.signedLayout.format v.payload).lanes
  rw [format]; rfl

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI

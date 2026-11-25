import OAI.Hierarchy.DescentPhysicalSignedLayout
import OAI.Hierarchy.DescentDatedSignedBill

namespace OAI
/-! # Native cost of the issued signed successor -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentStaticWordColumn
noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P)

theorem issued_feed_bill_at (I : v.withIssuedSigned.signed.Input) (base w K ratio : ℕ)
    (snippets : v.withIssuedSigned.signed.SnippetWork I K)
    (wide : 2*v.signedLayout.unit ≤ v.payload) (machine : w ≤ ratio*v.payload) :
    (v.withIssuedSigned.signed.phaseTicks I base w +
      7*names (v.withIssuedSigned.signed.phase I base w).program)*w ≤
      ratio*v.withIssuedSigned.signed.feedFactor K*
        v.withIssuedSigned.signed.feedVolume v.payload v.signedLayout.unit :=
  v.withIssuedSigned.signed.feed_bill I base w K v.payload v.signedLayout.unit ratio
    snippets (v.signedLayout.width v.payload) v.signedLayout.positive wide
    (v.signedLayout.lanes_eq v.payload) machine

theorem issued_feed_bill (I : v.withIssuedSigned.signed.Input) (floor w K ratio : ℕ)
    (snippets : v.withIssuedSigned.signed.SnippetWork I K)
    (wide : 2*v.signedLayout.unit ≤ v.payload) (machine : w ≤ ratio*v.payload) :
    (v.withIssuedSigned.signed.phaseTicks I (v.withIssuedSigned.peerTail floor) w +
      7*names (v.withIssuedSigned.signed.phase I (v.withIssuedSigned.peerTail floor) w).program)*w ≤
      ratio*v.withIssuedSigned.signed.feedFactor K*
        v.withIssuedSigned.signed.feedVolume v.payload v.signedLayout.unit :=
  v.issued_feed_bill_at I (v.withIssuedSigned.peerTail floor) w K ratio snippets wide machine

/-- The marked transition starts the signed scan after the actual venue and
mark programs. Its date, pitch, and source operands are those of the successor. -/
theorem issued_feed_mark_bill (I : v.withIssuedSigned.signed.Input) (floor w K ratio : ℕ)
    (snippets : v.withIssuedSigned.signed.SnippetWork I K)
    (wide : 2*v.signedLayout.unit ≤ v.payload) (machine : w ≤ ratio*v.payload) :
    (v.withIssuedSigned.signed.phaseTicks I (v.withIssuedSigned.markEnd floor) w +
      7*names (v.withIssuedSigned.signed.phase I (v.withIssuedSigned.markEnd floor) w).program)*w ≤
      ratio*v.withIssuedSigned.signed.feedFactor K*
        v.withIssuedSigned.signed.feedVolume v.payload v.signedLayout.unit :=
  v.issued_feed_bill_at I (v.withIssuedSigned.markEnd floor) w K ratio snippets wide machine

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI

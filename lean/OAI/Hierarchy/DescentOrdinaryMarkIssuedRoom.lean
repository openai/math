import OAI.Hierarchy.DescentOrdinaryMarkAfterHosts
import OAI.Hierarchy.DescentDatedSignedAny
import OAI.Hierarchy.DescentPhysicalSignedLayout

namespace OAI
/-! The earlier matcher and the installed signed layout fit the mark reader at this date. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentPacking.PackedMatch.Local.Stage
noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P)

theorem mark_room_of_signed (floor : ℕ) (input : Dated.Operands) {w : ℕ}
    (matcher : v.area.Space input w floor) (signed : v.SignedRoom floor w)
    (issued : v.withIssuedSigned = v) (radix : v.schedule.radix = 2^v.k) :
    v.MarkRoom floor input w := by
  have format : v.signedLayout.format v.payload = v.signed :=
    congrArg (fun state : PhysicalOrdinary F P => state.signed) issued
  have active : v.age < v.schedule.length := v.ticket.hubRows.choose
  have partition := Fintype.card_congr (v.schedule.groupDigits active radix)
  have groups : v.signed.groups*v.signed.blocks = v.schedule.groupCount v.age := by
    rw [← format]
    change v.schedule.groupCount (v.age+1)*2^v.k = v.schedule.groupCount v.age
    simpa only [Fintype.card_prod, Fintype.card_fin] using partition.symm
  have blocks : 0 < v.markShape.blocks := by
    change 0 < v.signed.blocks
    rw [← format]
    exact Nat.two_pow_pos _
  have upper : v.markEnd floor < 2^w :=
    (Nat.le_add_right ..).trans_lt signed.combined
  have before := (v.signed_stage_paid floor).1.trans (v.signed_stage_paid floor).2.1
  apply v.mark_room_at floor input signed.lanes blocks upper
  intro slot
  have original := v.mark_original_wires floor input groups matcher slot
  exact ⟨⟨original.1.1, original.1.2.1, original.1.2.2.trans before⟩, original.2⟩

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI

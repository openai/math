import OAI.Hierarchy.DescentDatedResetVenueRun
import OAI.Hierarchy.DescentNormalizedVenueLower

namespace OAI
/-! # The whole successor venue lies above the funded reset input -/
namespace Hierarchy.DescentDatedAddressBook.ResetVenue
open DescentSixParty DescentCompactVenuePeers
noncomputable section
variable (v:ResetVenue) (input:Earlier) (base:ℕ)

theorem sources_lower :
    base≤(v.sources input base).roster.base ∧ base≤(v.sources input base).hub.base ∧ base≤v.venueStart base:=by
  have early:= (v.after base).1
  obtain ⟨actors,peersAt,venue⟩:=v.steps base
  have old:base≤v.peerStart base:=(early.trans actors).trans peersAt
  have roster:v.peerStart base≤(v.sources input base).roster.base:=by
    simp only [sources,peers,slots,hosts]
    omega
  have hub:(v.sources input base).roster.base≤(v.sources input base).hub.base:=Nat.le_add_right ..
  exact ⟨old.trans roster,(old.trans roster).trans hub,old.trans venue⟩

theorem outputs_from (start:ℕ) (low:start≤base):
    VenueFrom (v.next.operands (v.sources input base) (v.venueStart base)) v.next.degree start:=by
  obtain ⟨roster,hub,issued⟩:=v.sources_lower input base
  exact v.next.venue_lower (v.sources input base) start (v.venueStart base)
    (low.trans issued) (low.trans roster) (low.trans hub)

/-- The native ID pages are allocated by an integer slot, independently of the
degree used by the returned consumer. -/
theorem outputs_from_degree (start:ℕ) (low:start≤base) (D:ℕ):
    VenueFrom (v.next.operands (v.sources input base) (v.venueStart base)) D start:=by
  have standard:=v.outputs_from input base start low
  refine ⟨?_,standard.roster,standard.offsets,standard.chunks,standard.actors,
    standard.signed,standard.hubs,standard.atoms⟩
  intro j
  obtain ⟨a,b,c,_⟩:=v.next.order (v.venueStart base)
  have cursor:=(((low.trans (v.sources_lower input base).2.2).trans a).trans b).trans c
  change start≤StageVenueTail.area _ _ _ _ _+_
  apply Nat.le_trans _ (Nat.le_add_right ..)
  change start≤DescentActorRaster.Venue.outBase _ _ _+_
  exact (cursor.trans (Nat.le_add_right ..)).trans (Nat.le_add_right ..)

end
end Hierarchy.DescentDatedAddressBook.ResetVenue

end OAI

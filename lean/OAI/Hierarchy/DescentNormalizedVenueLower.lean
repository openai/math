import OAI.Hierarchy.DescentStageVenueChange
import OAI.Hierarchy.DescentDatedVenueFrame

namespace OAI
/-! # Lower endpoints of every bank in a physically repacked successor venue -/
namespace Hierarchy.DescentSixParty.StageVenueTail.Date
open DescentPacking.PackedMatch.Local.Stage DescentSIMDLookup DescentPackedColony ProtocolRAM
noncomputable section

private theorem page_after (s : DescentVenueSlabs.Shape) (base j : ℕ) :
    base≤ (DescentVenueSlabs.page s base j).base:=by
  simp only [DescentVenueSlabs.page,Overlap.outputBank,Overlap.dest,Overlap.dictBase,DescentVenueSlabs.work]
  omega

theorem venue_lower (d : Date) (B : Sources) (src start : ℕ) (early : src≤ start)
    (roster : src≤ B.roster.base) (hub : src≤ B.hub.base) :
    VenueFrom (d.operands B start) d.degree src :=by
  let α:=d.thirdEnd start
  let β:=area α d.k d.hosts d.groups d.lanes
  obtain ⟨a,b,c,_⟩:=d.order start
  have before:src≤ α:=early.trans (a.trans (b.trans c))
  have actor:src≤ DescentActorRaster.Venue.outBase α d.k d.lanes:=
    before.trans (Nat.le_add_right ..)
  have cursor:src≤ β:=actor.trans (Nat.le_add_right ..)
  refine ⟨fun j=>cursor.trans (Nat.le_add_right ..),roster,?_,?_,actor,?_,hub,?_⟩
  · exact cursor.trans (Nat.le_add_right ..)
  · exact (cursor.trans (Nat.le_add_right ..)).trans (Nat.le_add_right ..)
  · intro x j
    exact early.trans (page_after _ _ _)
  · intro x
    exact ⟨early.trans (a.trans (page_after _ _ _)),True.intro⟩
end
end Hierarchy.DescentSixParty.StageVenueTail.Date

end OAI

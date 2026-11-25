import OAI.Hierarchy.DescentDatedResetVenue
import OAI.Hierarchy.DescentNamedFundedChart
import OAI.Hierarchy.DescentDatedActorSetup
import OAI.Hierarchy.DescentDatedPublicOutput

namespace OAI
/-! # Concrete physical dimensions of the reset-to-reached handover -/
namespace Hierarchy.DescentDatedAddressBook.ResetVenue
open DescentSixParty DescentCompiler DescentSIMDLookup DescentFundedCensus
open LinearAlgebra.SpectralBooks ThreeFlat RouteUnits Expander NonlinearExpanders
noncomputable section

def collect (old:StageVenueTail.Date)(census:Shape)(a:ActorSetup)(next:PublicOutput)(lanes:ℕ):ResetVenue where
  census:=census
  dense:=⟨census.jobs,census.hosts,next.hosts,next.groups,next.blocks,census.bits,census.lanes,next.lanes⟩
  next:=⟨old.k,next.hosts,next.groups,3,next.capacity,census.bits,next.lanes,next.lanes,next.lanes,lanes⟩
  actorLanes:=a.lanes

def fromBoard {n d:ℕ}(board:NonlinearExpanders.Graph n d)(old:StageVenueTail.Date)(middle:ResetMiddle)
    (a:ActorSetup)(next:PublicOutput)(f gain matcherLanes:ℕ):ResetVenue:=
  collect old (DescentNamedFundedChart.shape board old middle f gain) a next matcherLanes

end
end Hierarchy.DescentDatedAddressBook.ResetVenue

end OAI

import OAI.Hierarchy.DescentCompactVenuePeers
import OAI.Hierarchy.DescentDatedVenueRate
import OAI.Hierarchy.DescentVenueQuantityState
import OAI.Hierarchy.DescentFundedCensusRate

namespace OAI
/-! # The charged census and the next stage's physical source banks -/
namespace Hierarchy.DescentDatedAddressBook
open DescentSixParty Filter
noncomputable section

structure ResetVenue where
  census : DescentFundedCensus.Shape
  dense : DescentVenueQuantityPlanes.Dims
  next : StageVenueTail.Date
  actorLanes : ℕ := census.lanes

namespace ResetVenue
variable (v : ResetVenue)

def denseStart (base : ℕ) := v.census.roof base
def actorDims : DescentVenueQuantityPlanes.Dims := { v.dense with precision:=1,oldLanes:=v.actorLanes }
def rawHosts := v.dense.oldHosts*v.dense.shapes
def actorStart (base:ℕ) := DescentVenueQuantityPlanes.State.roof v.dense (v.denseStart base)
def peerStart (base:ℕ) := DescentVenueQuantityPlanes.State.roof v.actorDims (v.actorStart base)
def venueStart (base : ℕ) := DescentCompactVenuePeers.roof (v.peerStart base) v.rawHosts v.dense.hosts
def endAddress (base : ℕ) := v.next.endAddress (v.venueStart base)

theorem translated (base : ℕ) : v.endAddress base=base+v.endAddress 0 :=by
  rw [endAddress,endAddress,v.next.translates (v.venueStart base),v.next.translates (v.venueStart 0)]
  rw [venueStart,venueStart,DescentCompactVenuePeers.shift (v.peerStart base),DescentCompactVenuePeers.shift (v.peerStart 0)]
  unfold peerStart
  rw [DescentVenueQuantityPlanes.State.shift v.actorDims (v.actorStart base),
    DescentVenueQuantityPlanes.State.shift v.actorDims (v.actorStart 0)]
  unfold actorStart
  rw [DescentVenueQuantityPlanes.State.shift v.dense (v.denseStart base),
    DescentVenueQuantityPlanes.State.shift v.dense (v.denseStart 0)]
  rw [denseStart,v.census.shift base]
  simp only [denseStart,Nat.add_assoc]

theorem steps (base:ℕ):v.denseStart base≤v.actorStart base ∧ v.actorStart base≤v.peerStart base ∧
    v.peerStart base≤v.venueStart base:=by
  refine ⟨?_,?_,?_⟩
  · rw [actorStart,DescentVenueQuantityPlanes.State.shift];exact Nat.le_add_right ..
  · rw [peerStart,DescentVenueQuantityPlanes.State.shift];exact Nat.le_add_right ..
  · rw [venueStart,DescentCompactVenuePeers.shift];exact Nat.le_add_right ..

theorem after (base : ℕ) : base≤v.denseStart base ∧ v.denseStart base≤v.venueStart base ∧
    v.venueStart base≤v.endAddress base :=by
  refine ⟨v.census.room base,?_,?_⟩
  · exact (v.steps base).1.trans ((v.steps base).2.1.trans (v.steps base).2.2)
  · rw [endAddress,v.next.translates]
    exact Nat.le_add_right ..

variable {ι : ℕ→Type*} (p : ∀h,ι h→ResetVenue)
structure ScalarRoom : Prop where
  census : DescentFundedCensus.Shape.ScalarRoom (fun h i=>(p h i).census)
  dense : DescentVenueQuantityPlanes.State.ScalarRoom (fun h i=>(p h i).dense)
  actor : DescentVenueQuantityPlanes.State.ScalarRoom (fun h i=>(p h i).actorDims)
  next : StageVenueTail.Date.ScalarRoom (fun h i=>(p h i).next)

theorem extent_rate (b : ScalarRoom p) : Bounded (fun h i=>(p h i).endAddress 0) :=by
  have raw:=DescentFundedCensus.Shape.rate _ b.census
  have dense:=DescentVenueQuantityPlanes.State.extent_rate _ b.dense
  have venue:=StageVenueTail.Date.extent_rate _ b.next
  have actor:=DescentVenueQuantityPlanes.State.extent_rate _ b.actor
  have one:=Bounded.const (ι:=ι) 1
  have r:=((b.dense.oldHosts.mul b.dense.sheets).add one).padded
  have h:=b.dense.hosts
  have three:=(((Bounded.const (ι:=ι) 3).mul h).add one).padded
  have last:=(h.add one).padded
  apply (((((((raw.add dense).add actor).add r).add three).add three).add three).add last).add venue |>.of_le
  intro h i
  rw [endAddress,(p h i).next.translates,venueStart,DescentCompactVenuePeers.shift,peerStart,
    DescentVenueQuantityPlanes.State.shift,actorStart,DescentVenueQuantityPlanes.State.shift]
  simp [denseStart,DescentCompactVenuePeers.roof,DescentCompactVenuePeers.hubs,
    DescentCompactVenuePeers.peers,DescentCompactVenuePeers.slots,DescentCompactVenuePeers.hosts,
    DescentCompactVenuePeers.span,rawHosts,Nat.add_assoc]

end ResetVenue
end
end Hierarchy.DescentDatedAddressBook

end OAI

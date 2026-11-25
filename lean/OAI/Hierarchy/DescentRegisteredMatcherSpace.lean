import OAI.Hierarchy.DescentDatePortWireRoom
import OAI.Hierarchy.DescentDatePortPortRoom
import OAI.Hierarchy.DescentDatePortPaidRoom
import OAI.Hierarchy.DescentDonorMatcherSpace

namespace OAI
/-! The actual registered finite banks suffice for the ordinary matcher on arbitrary memory. -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentPackedColony DescentColonies DescentSIMDLookup DescentPacking.PackedMatch.Local.Stage
open ProtocolRAM
noncomputable section
variable (p:DatePorts) (d:DonorDate) (payload seats board w root floor:ℕ)
local notation "M" => lanes payload d.amount
local notation "a" => d.schedule payload seats board

theorem matcher_placement (wire:p.WireRoom w root) (ports:p.PortRoom w root) (header:p.HeaderRoom w root)
    (actor:p.ActorRoom w root) (paid:p.PaidRoom w root) (placed:root≤floor)
    (k:p.venue.k=d.exponent) (D:p.venue.degree=d.degree) (cap:p.venue.cap=d.cap)
    (H:p.venue.hosts=d.hosts) (G:p.venue.groups=d.groups) (pitch:p.venue.lanes=M)
    (positive:0<d.cap) (bits:board≤2^d.exponent) (homes:0<d.hosts)
    (lanesPaid:2*d.amount≤payload) (fits:payload≤w) (last:(a).rotationEnd p.io.roster floor<2^w) :
    (a).Space p.io w floor :=by
  have accessible:=(ports.mono placed).accessible (header.mono placed) (actor.mono placed)
  have previous:=wire.mono placed
  apply d.matcher_space payload seats board p.io w floor positive bits homes lanesPaid fits _ _ (header.mono placed).hubs _ last
  · rw [← D]
    simpa only [H,G,pitch] using accessible
  · intro x j
    let xx:Block p.venue.k:=Fin.cast (congrArg (2^·) k.symm) x
    let jj:Fin (2*p.venue.cap):=Fin.cast (congrArg (2*·) cap.symm) j
    have read:=previous xx jj
    change (p.io.wire x.val j.val).Fits w floor ∧ d.hosts*chunks d.groups M≤(p.io.wire x.val j.val).size
    simpa only [xx,jj,Fin.val_cast,H,G,pitch] using read
  · intro x;exact (paid.mono placed).stock x.val

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI

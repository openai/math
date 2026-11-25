import OAI.Hierarchy.DescentDatedPhysicalOrdinary
import OAI.Hierarchy.DescentSignedStageFormat

namespace OAI
/-! # The signed layout issued by an ordinary date -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook
noncomputable section

variable {F P : Type} [Field F] (v : PhysicalOrdinary F P)

/-- The two placements determine the socket capacities. The returned host
population and group count are those at the next calendar date. -/
def signedLayout : SignedStage where
  k := v.k
  oldDegree := v.prior.placement.degree
  oldCap := v.prior.placement.cap
  newDegree := v.target.placement.degree
  newCap := v.target.placement.cap
  oldHosts := v.area.H
  newHosts := v.venue.hosts
  groups := v.schedule.groupCount (v.age+1)
  radix := v.gadget.b
  colors := v.gadget.C
  padding := v.gadget.k

def withIssuedSigned : PhysicalOrdinary F P :=
  {v with signed := v.signedLayout.format v.payload}

/-- The reached placements give exactly the degree and capacity transition
used in the uniform stage tariff. -/
theorem signedLayout_eq :
    v.signedLayout =
      ⟨v.k,v.degree,v.prior.placement.cap,DescentCompiler.ordinaryDegree v.degree,
       2^DescentHostDegree.gainExponent 20 v.degree*v.gadget.b*v.prior.placement.cap,
       v.area.H,v.venue.hosts,v.schedule.groupCount (v.age+1),v.gadget.b,v.gadget.C,v.gadget.k⟩ := by
  simp only [signedLayout,v.prior.branch,v.target.branch,v.ticket.nextDegree,v.ticket.capacity]

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI

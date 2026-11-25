import OAI.Hierarchy.DescentOrdinaryBooksAtDate
import OAI.Hierarchy.DescentOrdinaryArgumentWidths
import OAI.Hierarchy.DescentNamedDonorOutputPorts

namespace OAI
/-! # A receiving program selected from the preceding date's actual registers -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentDatedAddressBook DescentDatedPriorOperand DescentSIMDLookup
open DescentPrimitivePalette DescentDatedOperandReadPipeline
noncomputable section

namespace DatePorts

/-- The seven archived fields are indexed at their producer's physical host
height and packing pitch. Their source may be a seed, ordinary, or reset date. -/
def argumentLayout (prior : DatePorts) (radix : ℕ) : Layout :=
  ⟨radix,prior.nodes,prior.argumentsPerNode,prior.operandHosts,prior.venue.groups,
    prior.operandLanes,prior.operandBits-2⟩

theorem argument_width (prior : DatePorts) (radix : ℕ) (width : 2≤prior.operandBits) :
    (prior.argumentLayout radix).size+2=prior.operandBits := Nat.sub_add_cancel width

end DatePorts

namespace PhysicalOrdinary
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P)

/-- The donor word is the result of the same matcher as the dated program.
The other three inputs and both archived books come from the preceding date. -/
def datedEntry (prior : DatePorts) (stageFloor : ℕ) : ArgumentEntry v :=
  let ports:=v.ticket.donorDate.outputPorts v.payload v.seats prior.io stageFloor v.bitsPerField
  { clip:=v.fundedClip 0
    venue:=⟨ports.packedDonors,prior.io.actors,prior.io.hubs,prior.io.roster⟩
    previous:=prior.argumentLayout (2^v.area.k)
    previousBase:=prior.archive.arguments
    rolePitch:=prior.roleLanes
    roleBits:=printedBits v.gadget v.palette.seedWidth v.palette.grainLimit v.palette.rotor
    role:=fun x=>prior.archive.roles.bank x.val }

/-- Both finite dictionaries use the widths of the normalized numerical
geometry. The pitch selected from these widths does not occur in them. -/
def argumentUnitFrom (prior : DatePorts) (stageFloor : ℕ) :=
  let A:=v.datedEntry prior stageFloor
  let W:=v.withFundedArguments 0 A
  max (v.fullArgumentUnit A) (purchase W.ticketReadGeometry)

def fundedFrom (prior : DatePorts) (stageFloor : ℕ) :=
  v.withFundedArguments (v.argumentUnitFrom prior stageFloor) (v.datedEntry prior stageFloor)

/-- The origin, newborn and raw source pages are allocated at the two selected
physical pitches and on the actual shifted matcher floor. -/
def registeredFrom (prior : DatePorts) (stageFloor : ℕ) :=
  (v.fundedFrom prior stageFloor).withOriginReservation

/-- Changing the final raw-source allocation preserves the earlier input banks. -/
def registeredEntry (prior : DatePorts) (stageFloor : ℕ) :
    ArgumentEntry (v.registeredFrom prior stageFloor) :=
  let A:=v.fundedEntry (v.argumentUnitFrom prior stageFloor) (v.datedEntry prior stageFloor)
  ⟨A.clip,A.venue,A.previous,A.previousBase,A.rolePitch,A.roleBits,A.role⟩

theorem registered_match (prior : DatePorts) (stageFloor : ℕ)
    (capacity : prior.argumentsPerNode≤v.vector.operands) :
    (v.registeredEntry prior stageFloor).Match (v.registeredFrom prior stageFloor) stageFloor :=
  by
    have m := v.funded_match (v.argumentUnitFrom prior stageFloor) (v.datedEntry prior stageFloor) stageFloor rfl capacity
    exact ⟨m.post, m.radix, m.refPitch, m.bornPitch, m.paths, m.oldBlocks, m.oldArgs,
      m.newBlocks, m.newCap, m.newArgs, m.atRefs⟩

theorem registered_reservation (prior : DatePorts) (stageFloor : ℕ) :
    let W:=v.registeredFrom prior stageFloor
    W.origin.preparationWords=W.originControlWords+W.originMouthWords+W.rootSourceSize :=rfl

theorem registered_geometry (prior : DatePorts) (stageFloor : ℕ) :
    (v.registeredFrom prior stageFloor).VectorShape :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem registered_node_chart (prior : DatePorts) (stageFloor : ℕ) :
    let W:=v.registeredFrom prior stageFloor
    W.metadata.chart=W.nodeChart ∧ W.operandBook=W.finalChart := ⟨rfl,rfl⟩

theorem registered_tape (prior : DatePorts) (stageFloor : ℕ) :
    let A:=v.registeredEntry prior stageFloor
    A.previous=prior.argumentLayout (2^v.area.k) ∧
    A.previousBase=prior.archive.arguments ∧
    A.rolePitch=prior.roleLanes ∧
    (∀x,A.role x=prior.archive.roles.bank x.val) ∧
    A.venue.panel=(v.ticket.donorDate.outputPorts v.payload v.seats prior.io stageFloor v.bitsPerField).packedDonors :=
  ⟨rfl,rfl,rfl,fun _=>rfl,rfl⟩

private theorem argumentWidths_reserved (u : PhysicalOrdinary F P) (a : ArgumentEntry u) :
    u.withOriginReservation.argumentWidths ⟨a.clip, a.venue, a.previous, a.previousBase, a.rolePitch, a.roleBits, a.role⟩ =
      u.argumentWidths a := by
  dsimp only [argumentWidths, widthTable, ArgumentEntry.population, ArgumentEntry.roleLayout,
    ArgumentEntry.chip, finalChart, nodeChart, originChart, withOriginReservation]
  rfl

private theorem purchase_funded (a : ArgumentEntry v) (extra : ℕ) :
    purchase (v.withFundedArguments extra a).withOriginReservation.ticketReadGeometry =
      purchase (v.withFundedArguments 0 a).ticketReadGeometry := by
  dsimp only [purchase, candidateLimit, candidateCount, ticketReadGeometry, operandShortBits,
    withOriginReservation, withFundedArguments, withFundedClip]
  rfl

theorem registered_width (prior : DatePorts) (stageFloor : ℕ) :
    let W:=v.registeredFrom prior stageFloor
    let A:=v.registeredEntry prior stageFloor
    (∀i,W.argumentWidths A i*A.clip.working≤v.payload/4) ∧
    purchase W.ticketReadGeometry*W.resolver.lanes≤v.payload/4 :=by
  let entry:=v.datedEntry prior stageFloor
  let other:=purchase (v.withFundedArguments 0 entry).ticketReadGeometry
  let extra := max (v.fullArgumentUnit entry) other
  let u := v.withFundedArguments extra entry
  let e := v.fundedEntry extra entry
  constructor
  · intro i
    change u.withOriginReservation.argumentWidths ⟨e.clip, e.venue, e.previous, e.previousBase, e.rolePitch, e.roleBits, e.role⟩ i*(v.fundedClip extra).working≤v.payload/4
    rw [argumentWidths_reserved u e]
    exact (v.funded_argument_widths entry other i).1
  · change purchase u.withOriginReservation.ticketReadGeometry*(v.fundedClip extra).postPitch≤v.payload/4
    rw [purchase_funded v entry extra]
    exact (v.funded_extra_fit extra other (le_max_right ..)).2.2

end PhysicalOrdinary
end
end Hierarchy.DescentSixParty.Chronology

end OAI

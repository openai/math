import OAI.Hierarchy.DescentRegisteredOrdinarySize
import OAI.Hierarchy.DescentDatedOperandSelectorUniform

namespace OAI
/-! # The public data consumed by the three input phases and the operand selector -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentDatedAddressBook DescentOrdinaryVenueIngress DescentHaloWalkRAM DescentSIMDLookup
open DescentDatedPriorOperand ProtocolRAM
noncomputable section
set_option quotPrecheck false

namespace PhysicalOrdinary
structure BareData where
  books : OrdinaryBooks
  clip : Clip
  venue : Inputs
  signedEnd : ℕ
  previous : Layout
  previousBase : ℕ
  rolePitch : ℕ
  roleBits : ℕ
  role : ℕ→Bank
  demand : ℕ
  grain : ℕ

namespace BareData
variable (r : BareData)
structure Valid : Prop where
  paths : r.clip.venue.paths=breadth r.books.reference.degree
  oldBlocks : r.previous.blocks=2^r.books.reference.k
  oldArgs : r.previous.operands≤r.books.vector.operands
  newBlocks : r.books.bornBook.blocks=2^r.books.reference.k
  newCap : r.books.bornBook.cap=r.books.reference.capacity
  newArgs : r.books.bornBook.args=r.books.vector.operands

def plan (h : r.Valid) : ArgumentPlan where
  clip:=r.clip
  venue:=r.venue
  signedEnd:=r.signedEnd
  previous:=r.previous
  previousBase:=r.previousBase
  rolePitch:=r.rolePitch
  roleBits:=r.roleBits
  role:=fun x=>r.role x.val
  demand:=r.demand
  reference:=r.books.reference
  refsStart:=r.signedEnd+r.books.ingressWords
  born:=r.books.bornBook
  vector:=r.books.vector
  resolver:=r.books.resolver
  origin:=r.books.origin
  grain:=r.grain
  source:=fun _ _=>.row
  paths:=h.paths
  oldBlocks:=h.oldBlocks
  oldArgs:=h.oldArgs
  newBlocks:=h.newBlocks
  newCap:=h.newCap
  newArgs:=h.newArgs

theorem plan_eq {s : BareData} (hr : r.Valid) (hs : s.Valid) (e : r=s) : r.plan hr=s.plan hs :=by
  cases e
  rfl
end BareData

variable {F : Type} [Field F]
def bareData (G : PoweredGadget F) (S : DescentCompiler.AtomSchedule) (age payload seats floor paidBits : ℕ)
    (ports : DatePorts) (core : StaticCore) (b : OrdinaryBooks) (c : Clip) : BareData :=
  let donor:=(core.donor.outputPorts payload seats ports.io floor paidBits).packedDonors
  let role:=DescentPrimitivePalette.printedBits G b.palette.seedWidth b.palette.grainLimit b.palette.rotor
  ⟨b,c,⟨donor,ports.io.actors,ports.io.hubs,ports.io.roster⟩,core.prefixProgram.endAddress,
    ports.argumentLayout (2^core.area.k),ports.archive.arguments,ports.roleLanes,role,ports.archive.roles.bank,
    G.b,DescentDatedPublicGrain.amount S G.b age⟩

variable {P : Type} (v : PhysicalOrdinary F P) (ports : DatePorts) (floor : ℕ)
local notation "W" => v.registeredFrom ports floor
local notation "A" => v.registeredEntry ports floor
local notation "data₀" => bareData v.gadget v.schedule v.age v.payload v.seats floor v.bitsPerField ports
  (v.staticCore floor) (W).books (A).clip

theorem registered_bare_valid (paid : ports.argumentsPerNode≤v.vector.operands) : (data₀).Valid :=
  let m:=v.registered_match ports floor paid
  ⟨m.paths,m.oldBlocks,m.oldArgs,m.newBlocks,m.newCap,m.newArgs⟩

theorem registered_bare_plan (paid : ports.argumentsPerNode≤v.vector.operands) :
    (W).bareArguments floor (A) (v.registered_match ports floor paid)=
      (data₀).plan (v.registered_bare_valid ports floor paid) :=rfl

end PhysicalOrdinary
end
end Hierarchy.DescentSixParty.Chronology

end OAI

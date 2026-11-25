import OAI.Hierarchy.DescentOrdinaryFundedProgram
import OAI.Hierarchy.DescentRegisteredOrdinaryBooks

namespace OAI
/-! # The two returned portions of a named ordinary date from its registered allocator -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentDatedAddressBook DescentOrdinaryVenueIngress DescentPacking.PackedMatch.Local.Stage
open StageVenueTail DescentSIMDLookup ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section

namespace PhysicalOrdinary.StaticCore
variable (c:StaticCore) (installed:OrdinaryBooks) (d:Date) (clip:Clip)

/-- The only data after the original numeric core are the registered allocation,
the normalized venue and the receiver that produced its local fields. -/
def returnChart:OrdinaryReturn:=
  ⟨c.area,c.material,c.signed,d,clip.working,installed.ingressWords,installed.reference,
    installed.bornBook,installed.vector,installed.origin.routeWords,installed.resolver⟩

end PhysicalOrdinary.StaticCore
namespace VenueProgram
variable (c:OrdinaryReturn) (donor:ℕ)
def signedEnd:=c.signed.roof (c.markEnd donor)
def vectorStart:=c.born.endAddress (signedEnd c donor+c.ingressWords+c.reference.extent)
def returned (metadata:MetadataReturn):ReturnProgram:=
  ⟨c.venue,c.sources donor,metadata,c.resolver,c.rasterEnd donor,c.vector.out (vectorStart c donor),
    c.vector.endAddress (vectorStart c donor)+c.routeWords⟩

def funded (clip:Clip) (paths:clip.venue.paths=OrdinaryRaster.paths c.area) (input:Dated.Operands) (w:ℕ):PrintedStep w:=
  FundedProgram.fromChart c donor (clip.fieldBank (signedEnd c donor))
    (paths ▸ clip.ports (signedEnd c donor)) input w

theorem funded_eq {other:OrdinaryReturn} (same:c=other) (clip:Clip)
    (left:clip.venue.paths=OrdinaryRaster.paths c.area) (right:clip.venue.paths=OrdinaryRaster.paths other.area)
    (input:Dated.Operands) (w:ℕ):funded c donor clip left input w=funded other donor clip right input w:=by
  subst other
  rfl

/-- The same two original instruction streams and timestamps on either side of the
venue return. Both read positions come from the registered field shelf. -/
def printReturn (w:ℕ) (metadata:MetadataReturn):PrintedStep w:=
  let op:=returned c donor metadata
  ⟨op.instructions w,op.clock w⟩
/-- The path count in the actual clipped directory is the one used in the purchased
funded scan. Its proof carries no program choices. -/
@[ext] structure Registered where
  core : PhysicalOrdinary.StaticCore
  installed : OrdinaryBooks
  venue : Date
  clip : Clip
  paths : clip.venue.paths=OrdinaryRaster.paths core.area

namespace Registered
variable (b:Registered)
def chart:=b.core.returnChart b.installed b.venue b.clip
def fundedCode (input:Dated.Operands)(w:ℕ):PrintedStep w:=
  funded b.chart b.core.donorEnd b.clip b.paths input w
def returnCode (w:ℕ):PrintedStep w:=printReturn b.chart b.core.donorEnd w b.installed.metadata
end Registered
end VenueProgram

namespace PhysicalOrdinary
variable {F P:Type} [Field F] (v:PhysicalOrdinary F P)

theorem registered_return_chart (floor:ℕ) (A:ArgumentEntry v) (pitch:v.rasterLanes=A.clip.working):
    v.returnChart=(v.staticCore floor).returnChart v.books v.venue A.clip:=by
  unfold returnChart StaticCore.returnChart
  simp only [pitch,staticCore,books,routeWords]

theorem return_from_chart (floor:ℕ) :
    v.returnProgram floor (v.reachedSources floor)=VenueProgram.returned v.returnChart (v.donorEnd floor) v.metadata:=rfl

theorem registered_venue_programs (floor:ℕ) (A:ArgumentEntry v) (input:Dated.Operands) (w:ℕ)
    (paths:A.clip.venue.paths=OrdinaryRaster.paths v.area)
    (fund:v.FundedRoom floor (v.fundedFromEntry floor A paths) input w)
    (result:v.ResultRoom floor (v.reachedSources floor) w):
    PrintedStep.ofPhase (v.fundedRaster floor (v.fundedFromEntry floor A paths) input w fund)=
      VenueProgram.funded v.returnChart (v.donorEnd floor) A.clip paths input w ∧
    PrintedStep.ofPhase (v.returnPhase floor (v.reachedSources floor) w result)=
      VenueProgram.printReturn v.returnChart (v.donorEnd floor) w v.metadata:=⟨rfl,rfl⟩

def returnRegisters (floor:ℕ) (A:ArgumentEntry v) (paths:A.clip.venue.paths=OrdinaryRaster.paths v.area) :
    VenueProgram.Registered:=⟨v.staticCore floor,v.books,v.venue,A.clip,paths⟩

theorem returned_registers (floor:ℕ) (A:ArgumentEntry v) (input:Dated.Operands) (w:ℕ)
    (paths:A.clip.venue.paths=OrdinaryRaster.paths v.area) (pitch:v.rasterLanes=A.clip.working)
    (fund:v.FundedRoom floor (v.fundedFromEntry floor A paths) input w)
    (result:v.ResultRoom floor (v.reachedSources floor) w):
    let b:=v.returnRegisters floor A paths
    PrintedStep.ofPhase (v.fundedRaster floor (v.fundedFromEntry floor A paths) input w fund)=b.fundedCode input w ∧
      PrintedStep.ofPhase (v.returnPhase floor (v.reachedSources floor) w result)=b.returnCode w:=by
  intro b
  have eq:v.returnChart=b.chart:=v.registered_return_chart floor A pitch
  have actual:=v.registered_venue_programs floor A input w paths fund result
  constructor
  · exact actual.1.trans (VenueProgram.funded_eq v.returnChart (v.donorEnd floor) eq A.clip paths b.paths input w)
  · refine actual.2.trans ?_
    change VenueProgram.printReturn v.returnChart (v.donorEnd floor) w v.metadata=
      VenueProgram.printReturn b.chart (v.donorEnd floor) w v.metadata
    rw [eq]

end PhysicalOrdinary
end
end Hierarchy.DescentSixParty.Chronology

end OAI

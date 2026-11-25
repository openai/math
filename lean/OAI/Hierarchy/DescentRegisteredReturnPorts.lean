import OAI.Hierarchy.DescentRegisteredReturnProgram

namespace OAI
/-! # All outgoing ordinary ports, including the complete primitive book and selector count -/
namespace Hierarchy.DescentSixParty.Chronology.VenueProgram
open DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage StageVenueTail
open DescentPrimitivePalette DescentOrdinaryPrimitiveCheckpoint ProtocolRAM
noncomputable section
variable {F:Type} [Field F] (G:PoweredGadget F)
variable (c:OrdinaryReturn)(donor:ℕ)(b:OrdinaryBooks)

def primitiveLayout:DescentOrdinaryPrimitiveCheckpoint.Layout:=
  ⟨b.vector.hosts,b.reference.degree,b.reference.k,b.reference.capacity,b.vector.lows,b.vector.groups,
   b.reference.oldNodes,b.resolver.nodes,printedBits G b.palette.seedWidth b.palette.grainLimit b.palette.rotor,
   Nat.clog 2 (b.reference.nodes+1),c.work,b.bornBook.lanes,b.vector.lanes,b.palette.workLanes,b.palette.nextLanes⟩

def metaStart:=c.venue.endAddress (c.rasterEnd donor)
def metaEnd:=b.metadata.ordinaryEnd (metaStart c donor)
def operandEnd:=b.operandBook.endAddress (metaEnd c donor b)
def primitiveStart:=DescentOrdinaryPaletteBirth.roof b.bornBook (operandEnd c donor b)
def primitiveEnd:=(primitiveLayout G c b).roof (primitiveStart c donor b)
def countAddress:=DescentOrdinaryCountScan.address (c.area.shapeAt.outputBits*c.area.lanesAt)
    (primitiveEnd G c donor b) c.area.batch
def endAddress:=DescentOrdinaryCountScan.endAddress (c.area.shapeAt.outputBits*c.area.lanesAt)
    (primitiveEnd G c donor b) c.area.batch

def priorRoles:PriorRolePages:=
  let p:=primitiveLayout G c b
  let d:=p.durable
  ⟨d.output (p.durableStart (primitiveStart c donor b)),d.rows,Nat.clog 2 (d.rows+1),d.blocks⟩

def nextPorts:DatePorts:=
  let result:=returned c donor b.metadata
  let size:=b.resolver.size+2
  let nodeBase:=result.node.inputsEnd (result.node.digitEnd (metaStart c donor) size) b.metadata.paidBits size
  let count:=DescentOrdinaryPeerCount.newCount (c.materialEnd donor) c.area.H c.area.D c.venue.hosts c.venue.degree
  let saved:PriorResetArchive:=⟨nodeBase,result.finished.out (metaEnd c donor b),false,priorRoles G c donor b,count⟩
  ⟨saved,c.venue,c.venue.operands (c.sources donor) (c.rasterEnd donor),
    b.resolver.size+2,b.resolver.lanes,b.resolver.operands,b.resolver.nodes,b.palette.nextLanes,b.resolver.hosts,(primitiveLayout G c b).primitiveBits⟩

namespace Registered
variable (r:Registered)
def next:=nextPorts G r.chart r.core.donorEnd r.installed
def selector:=countAddress G r.chart r.core.donorEnd r.installed
def roof:=endAddress G r.chart r.core.donorEnd r.installed
end Registered
end
end Hierarchy.DescentSixParty.Chronology.VenueProgram

namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open StageVenueTail DescentDatedAddressBook
noncomputable section
variable {F P:Type} [Field F] (v:PhysicalOrdinary F P)

theorem ports_from_chart (stage:ℕ):
    DatePorts.ordinary v stage=VenueProgram.nextPorts v.gadget v.returnChart (v.donorEnd stage) v.books:=rfl

theorem selector_from_chart (root:ℕ):
    v.countAddr root=VenueProgram.countAddress v.gadget v.returnChart (v.donorEnd (v.stageStart root)) v.books ∧
    v.fullEnd root=VenueProgram.endAddress v.gadget v.returnChart (v.donorEnd (v.stageStart root)) v.books:=⟨rfl,rfl⟩

theorem registered_return_ports (root:ℕ) (A:ArgumentEntry v)
    (paths:A.clip.venue.paths=OrdinaryRaster.paths v.area) (pitch:v.rasterLanes=A.clip.working):
    let stage:=v.stageStart root
    let r:=v.returnRegisters stage A paths
    DatePorts.ordinary v stage=r.next v.gadget ∧ v.countAddr root=r.selector v.gadget ∧ v.fullEnd root=r.roof v.gadget:=by
  intro stage r
  have layout:v.returnChart=r.chart:=v.registered_return_chart stage A pitch
  obtain ⟨selected,roof⟩:=v.selector_from_chart root
  exact ⟨(v.ports_from_chart stage).trans (congrArg (fun c=>VenueProgram.nextPorts v.gadget c (v.donorEnd stage) v.books) layout),
    selected.trans (congrArg (fun c=>VenueProgram.countAddress v.gadget c (v.donorEnd stage) v.books) layout),
    roof.trans (congrArg (fun c=>VenueProgram.endAddress v.gadget c (v.donorEnd stage) v.books) layout)⟩

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI

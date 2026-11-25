import OAI.Hierarchy.DescentMaterialSocketProgram
import OAI.Hierarchy.DescentDatedPriorHeaderPorts
import OAI.Hierarchy.DescentDatedOrdinarySignedInvoice
import OAI.Hierarchy.DescentOrdinaryMarkPhase
import OAI.Hierarchy.DescentOrdinaryMarkShape
import OAI.Hierarchy.DescentOrdinaryPeerRows
import OAI.Hierarchy.DescentOrdinaryVenueExtent

namespace OAI
/-! # The common numerical program following every ordinary matching date -/
namespace Hierarchy.DescentDatedAddressBook
open DescentSixParty.Chronology DescentRawCablePanel DescentSIMDLookup DescentPackedColony
open DescentHaloWalkRAM ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
noncomputable section

structure SignedProgram where
  signed : SignedExtent
  material : MaterialProgram
  marked : DescentOrdinaryMarkProject.Shape
  priorHosts : ℕ
  priorDegree : ℕ
  nextHosts : ℕ
  nextDegree : ℕ
  entry : ℕ

namespace SignedProgram
variable (v : SignedProgram)
def beginAt := PriorHeader.endAddress v.priorHosts v.signed.groups v.signed.lanes v.signed.degree v.entry
def afterMaterial := v.material.extent.endAddress v.beginAt
def afterPeers := DescentOrdinaryVenueReturn.roof v.afterMaterial v.priorHosts v.priorDegree v.nextHosts v.nextDegree
def afterMark := v.marked.endAddress v.afterPeers
def endAddress := v.signed.roof v.afterMark

structure Chart : Prop where
  degree : v.signed.degree=v.material.depot.degree
  blocks : v.signed.blocks=v.material.extent.blocks
  seats : v.signed.residentSlots=DepotRAM.Material.roles v.material.depot
  markSlots : v.signed.residentSlots=v.marked.slots

def input (c : v.Chart) : v.signed.Input :=
  let geo:=PriorHeader.rankBanks v.priorHosts v.signed.groups v.signed.lanes v.signed.degree v.entry
  let ports:=PriorHeader.ports v.priorHosts v.signed.groups v.signed.lanes v.signed.degree v.entry
  let seat (o : Fin v.signed.residentSlots):=(DepotRAM.Material.seatIndex v.material.depot).symm (Fin.cast c.seats o)
  let recv (z:v.signed.Socket) (f:Fin 9):=
    let j : Fin v.signed.reach × Fin v.signed.residentSlots := finProdFinEquiv.symm z.2
    v.material.materialSocket v.beginAt geo (cast (congrArg Ports (congrArg breadth c.degree)) ports)
      (Fin.cast (congrArg breadth c.degree) j.1) (seat j.2) (Fin.cast c.blocks z.1) f
  let launch (x:Fin v.signed.blocks) (o:Fin v.signed.residentSlots) (low:Bool):=
    v.material.originSocket v.beginAt (seat o) (Fin.cast c.blocks x) low
  {newDegree:=v.nextDegree,hostPitch:=v.material.setup.hostPitch,rankBanks:=geo,path:=fun z=>recv z 2,
   endpoints:=fun z b=>recv z (if b then 1 else 0),donor:=fun z i=>recv z ⟨3+i.val,by omega⟩,
   mark:=fun z=>DescentOrdinaryMarkProject.markExpr (v.marked.markStart v.afterPeers) v.signed.reach v.marked.slots
      v.priorHosts v.signed.hosts v.signed.groups v.signed.blocks v.marked.degree v.marked.cap v.marked.oldLanes v.signed.lanes z.1
      (Fin.cast (congrArg (fun y=>v.signed.reach*y) c.markSlots) z.2),
   priorRanks:=PriorHeader.priorRanks v.priorHosts v.signed.groups v.signed.lanes v.signed.degree v.entry,
   priorEnds:=PriorHeader.priorEnds v.priorHosts v.signed.groups v.signed.lanes v.signed.degree v.entry,
   newNeighbors:=DescentOrdinaryPeerRows.peers v.afterMaterial v.priorHosts v.priorDegree v.nextHosts v.nextDegree,
   donorForward:=fun x o=>launch x o false,donorLow:=fun x o=>launch x o true,
   reversePath:=PriorHeader.reversePath v.priorHosts v.signed.groups v.signed.lanes v.signed.degree v.entry,ports:=ports}

def signedPhase (c : v.Chart) (w : ℕ) := v.signed.phase (v.input c) v.afterMark w

end SignedProgram
end
end Hierarchy.DescentDatedAddressBook

end OAI

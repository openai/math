import OAI.Hierarchy.DescentOrdinaryVenueClipNumbers
import OAI.Hierarchy.DescentMaterialActorPair
import OAI.Hierarchy.DescentScalarHaloProgram
import OAI.Hierarchy.DescentScalarVenueRaster

namespace OAI
/-! # Fixed physical addresses of the ordinary receiving roster and ticket columns -/
namespace Hierarchy.DescentOrdinaryVenueIngress
open DescentSIMDLookup DescentRawCablePanel DescentHaloWalkRAM DescentPackedColony DescentScalarVenueMask
open ProtocolRAM
noncomputable section

structure Inputs where
  panel : Bank
  actors : Bank
  hub : Bank
  adjacency : Bank

namespace Chart
variable (v : Chart)
def rows:=v.hosts*chunks v.groups v.lanes
def rankWidth:=Nat.clog 2 v.rows
/-- The first three equally sized banks broadcast the scalar host-hub flag. -/
def actorBase (base : ℕ):=base+3*2^v.rankWidth
def haloBase (base : ℕ):=DepotRAM.ActorInputs.roof v.socket v.hosts v.groups v.lanes (v.actorBase base)
def rasterBase (base : ℕ):=DescentScalarHaloProgram.stop v.hosts v.groups v.lanes v.socket.degree (v.haloBase base)
def packedHub (base : ℕ):Bank:=⟨base+2*2^v.rankWidth,v.rankWidth⟩
def shape (base : ℕ) : Raster.Shape v.paths v.socket.blocks v.socket.cap :=
  let route:=DepotRAM.ActorInputs.routeStart v.socket v.hosts v.groups v.lanes (v.actorBase base)
  let key:=DepotRAM.ActorInputs.keyStart v.socket v.hosts v.groups v.lanes (v.actorBase base)
  ⟨DescentScalarHaloProgram.ports v.hosts v.groups v.lanes v.socket.degree (v.haloBase base),
    fun x j=>DepotRAM.ActorInputs.bank v.socket v.hosts v.groups v.lanes route (x,j),
    fun x j=>DepotRAM.ActorInputs.bank v.socket v.hosts v.groups v.lanes key (x,j),
    v.packedHub base,DescentScalarHaloProgram.ends v.hosts v.groups v.lanes v.socket.degree (v.haloBase base)⟩
def fieldBank (base : ℕ):Bank:=⟨Raster.output v.paths v.socket.blocks v.socket.cap v.raw v.names v.hosts v.groups v.lanes (v.rasterBase base),v.rankWidth⟩
def endAddress (base : ℕ):=(v.fieldBank base).base+(v.fieldBank base).size

theorem rowRoom : v.rows≤2^v.rankWidth:=Nat.le_pow_clog (by decide) _

theorem translated (base : ℕ) : v.endAddress base=base+v.endAddress 0 :=by
  have before:=DepotRAM.ActorInputs.translates v.socket v.hosts v.groups v.lanes (v.actorBase base)
  have zero:=DepotRAM.ActorInputs.translates v.socket v.hosts v.groups v.lanes (v.actorBase 0)
  simp only [endAddress,fieldBank,Bank.size,rasterBase,DescentScalarHaloProgram.stop,DescentScalarHaloProgram.ranksBase,
    DescentScalarHaloProgram.endsBase,DescentScalarHaloPortROM.stop,DescentScalarHaloProgram.statics,haloBase,
    Raster.output,Receiver.header,Headers.post,Headers.rom,Headers.afterHeaders,
    Headers.start,DescentPackedChildNeighbor.SIMD.ROM.output]
  rw [before,zero]
  simp only [actorBase,Nat.zero_add,Nat.add_assoc]

end Chart
end
end Hierarchy.DescentOrdinaryVenueIngress

end OAI

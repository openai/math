import OAI.Hierarchy.DescentOrdinaryVenueClipNumbers
import OAI.Hierarchy.DescentOrdinaryVenueIngressChart
import OAI.Hierarchy.DescentOverlapTables

namespace OAI
/-! # Packed row width and two incoming conversions for the ordinary venue raster -/
namespace Hierarchy.DescentOrdinaryVenueIngress
open DescentSIMDLookup DescentScalarVenueMask DescentRawCablePanel DescentSharedCableNames ProtocolRAM
noncomputable section

namespace Clip
variable (c : Clip)
theorem grouped : c.working=c.postPitch*2^c.venue.k:=rfl
def core : Chart:={c.venue with lanes:=c.working}
def peerBits:=DepotRAM.totalBits c.venue.socket
def actorBits:=1*c.venue.socket.blocks
def actorStart (base : ℕ):=Overlap.endAddress base c.venue.hosts c.venue.groups c.panelPitch c.working c.peerBits
def setupStart (base : ℕ):=Overlap.endAddress (c.actorStart base) c.venue.hosts c.venue.groups c.actorPitch c.working c.actorBits
def clipped (base : ℕ) (B : Inputs) : Inputs:=
  let v:=c.venue;let bits:=Overlap.mapBits v.hosts v.groups c.working
  ⟨⟨Overlap.dest base v.hosts v.groups c.panelPitch c.working c.peerBits,bits⟩,
   ⟨Overlap.dest (c.actorStart base) v.hosts v.groups c.actorPitch c.working c.actorBits,bits⟩,B.hub,B.adjacency⟩
def fieldBank (base : ℕ):=(c.core).fieldBank (c.setupStart base)
def ports (base : ℕ):=((c.core).shape (c.setupStart base)).ports
def fullEnd (base : ℕ):=(c.core).endAddress (c.setupStart base)

theorem translated (base : ℕ):c.fullEnd base=base+c.fullEnd 0:=by
  unfold fullEnd
  rw [(c.core).translated (c.setupStart base),(c.core).translated (c.setupStart 0)]
  simp [setupStart,actorStart,Overlap.endAddress,Overlap.dest,Overlap.dictBase,Nat.add_assoc]

theorem post_pos (panel : c.radix≤c.panelPitch) (actor : c.radix≤c.actorPitch) (wide : 4*c.unit*c.radix≤c.payload) : 0<c.postPitch:=by
  have nonzero : 0<c.unit:=(show 0<c.localUnit from (by decide : 0<2).trans_le (Nat.le_max_left ..)).trans_le (Nat.le_max_left ..)
  have rad : 0<c.radix:=Nat.two_pow_pos _
  have eqn : 2*(2*c.unit*c.radix)=4*c.unit*c.radix:=by ring
  exact Nat.lt_min.mpr ⟨Nat.div_pos panel rad,Nat.lt_min.mpr ⟨Nat.div_pos actor rad,
    Nat.div_pos (by rw [eqn];exact wide) (Nat.mul_pos (by decide) (Nat.mul_pos (Nat.mul_pos (by decide) nonzero) rad))⟩⟩

theorem working_pos (panel : c.radix≤c.panelPitch) (actor : c.radix≤c.actorPitch) (wide : 4*c.unit*c.radix≤c.payload) : 0<c.working:=
  Nat.mul_pos (c.post_pos panel actor wide) (Nat.two_pow_pos _)

theorem receiver_aperture : Receiver.unit c.venue.raw c.venue.names c.actorCount*c.working≤c.payload/4 :=by
  have bound : Receiver.unit c.venue.raw c.venue.names c.actorCount≤c.localUnit :=
    (Nat.le_max_right ..).trans ((Nat.le_max_right ..).trans ((Nat.le_max_right ..).trans (Nat.le_max_right ..)))
  rw [Nat.mul_comm];exact (Nat.mul_le_mul_left _ (bound.trans (Nat.le_max_left ..))).trans c.working_fields.2.2

end Clip
end
end Hierarchy.DescentOrdinaryVenueIngress

end OAI

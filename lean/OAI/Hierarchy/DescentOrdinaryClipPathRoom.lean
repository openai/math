import OAI.Hierarchy.DescentScalarPathTableRoom
import OAI.Hierarchy.DescentOrdinaryVenueClip

namespace OAI
/-! # All dated path names fit the word used to address their actual return book -/
namespace Hierarchy.DescentOrdinaryVenueIngress.Clip
open DescentSharedCableNames DescentScalarVenueMask
noncomputable section

theorem paths_fit (c : Clip) (base : ℕ) {w : ℕ} (room : c.fullEnd base<2^w) :
    c.venue.paths<2^w :=by
  let P:=c.venue.paths
  let a:=Packed.bits P
  let M:=c.working
  let H:=c.venue.hosts
  let G:=c.venue.groups
  have cap:=DescentPackedChildNeighbor.SIMD.ROM.paths_le_cells P a 1 M H G
  let r:=(c.core).rasterBase (c.setupStart base)
  let header:=Receiver.header r c.core.raw c.core.names M
    (DescentPackedActorMask.actors (P*c.core.socket.blocks) c.core.socket.cap)
  have terminal : P≤Headers.post header H G M P :=by
    change P≤Headers.rom header H P+DescentPackedChildNeighbor.SIMD.ROM.cells P a 1 M H G+
      2^(DescentPackedChildNeighbor.SIMD.ROM.rowBits H G M)
    exact cap.trans ((Nat.le_add_left _ _).trans (Nat.le_add_right _ _))
  apply lt_of_le_of_lt _ room
  exact terminal.trans (Nat.le_add_right ..)

end
end Hierarchy.DescentOrdinaryVenueIngress.Clip

end OAI

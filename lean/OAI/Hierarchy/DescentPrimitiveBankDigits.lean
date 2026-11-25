import OAI.Hierarchy.DescentOrdinaryPalettePosted
import OAI.Hierarchy.DescentOperandLaneRead

namespace OAI
/-! Physical two-level digit extraction at a real or padded node of the immutable ordinary primitive archive. -/
namespace Hierarchy.DescentOrdinaryPrimitiveCheckpoint.Layout
open DescentSIMDLookup DescentPackedColony ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {w : ℕ} (L : Layout) (S : L.Stock)
def digitAt (b : Bank) (m : Memory w) (live : 0<L.nextLanes)
    (h : Fin L.successors) (g : Fin L.groups) (n : Fin L.newNodes) :=
  digit L.primitiveBits n.val (digit (L.primitiveBits*L.newNodes) (lane g live).val
    (m (b.base+(row L.successors L.groups L.nextLanes (position h g live)).val)).val)

theorem read_digit (x : Fin L.blocks) (b : Bank) (m : Memory w) (live : 0<L.nextLanes)
    (room : (L.primitiveBits*L.newNodes)*L.nextLanes≤w) (read : Reads b (S.output x) L.nextLanes m)
    (h : Fin L.successors) (g : Fin L.groups) (n : Fin L.newNodes) :
    L.digitAt b m live h g n=((encode L.primitiveBits L.newNodes).symm (S.output x h g) n).val:=by
  have one:=DescentOperandStateBanks.Reset.lane_read b.base (S.output x) m read room live h g
  unfold digitAt
  rw [one]
  simpa only [Equiv.apply_symm_apply] using digit_encode ((encode L.primitiveBits L.newNodes).symm (S.output x h g)) n

theorem read_node (x : Fin L.blocks) (b : Bank) (m : Memory w) (live : 0<L.nextLanes)
    (room : (L.primitiveBits*L.newNodes)*L.nextLanes≤w) (read : Reads b (S.output x) L.nextLanes m)
    (h : Fin L.successors) (g : Fin L.groups) (n : Fin L.newNodes) (z : Fin L.candidates)
    (stamp : ((encode L.originBits L.newNodes).symm (S.origin x h g) n).val=z.val+1) :
    L.digitAt b m live h g n=(S.cells (finProdFinEquiv.symm h).1 (finProdFinEquiv (g,x)) z).val:=by
  rw [read_digit L S x b m live room read h g n,S.node x h g n z stamp]

theorem read_hole (x : Fin L.blocks) (b : Bank) (m : Memory w) (live : 0<L.nextLanes)
    (room : (L.primitiveBits*L.newNodes)*L.nextLanes≤w) (read : Reads b (S.output x) L.nextLanes m)
    (h : Fin L.successors) (g : Fin L.groups) (n : Fin L.newNodes)
    (stamp : ((encode L.originBits L.newNodes).symm (S.origin x h g) n).val=0) :
    L.digitAt b m live h g n=0:=by
  rw [read_digit L S x b m live room read h g n,S.hole x h g n stamp]
  exact Fin.val_zero _

end
end Hierarchy.DescentOrdinaryPrimitiveCheckpoint.Layout

end OAI

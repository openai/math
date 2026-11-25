import OAI.Computability.BorderVNP.DiagonalTallyGadgetHandoff
import OAI.Computability.BorderVNP.FiniteEvaluatorCubeReadLocation

namespace OAI
namespace Computability
namespace BorderVNP

set_option autoImplicit false

/-! # Address regions of the genuine signed lookup after the owned schedule -/

namespace RoutingISA.SignedTaskArena

open VPVNP.BurstRAM FiniteEvaluator DiagonalTallyPacketEmit BorderVNP.Cube BorderVNP.Cube.Tally
open BorderVNP.Cube.Padding.Banks

variable {w : ℕ} (a : Layout) (pub : Arg → Word w) (owner : Fin a.cube.header.d → ℕ)
    (team demand : ℕ) (A : Data a.cube.n a.cube.header.d a.cube.header.blocks a.cube.b a.cube.h a.cube.K a.cube.s)

/-- Every read of the raw gadget ID computation, including its selected
packet-bank references, lies in one of the three actual signed-arena regions. -/
theorem gadgetLookup_readAt {addr : ℕ} (packet : A.packetBase=a.cube.header.packetBase)
    (read : CubePacket.ReadAt (gadgetLookup a pub owner team demand A) pub addr) :
    (∃ j ∈ CubePacket.frameWords, addr=(pub 0).val+j) ∨
    (a.cube.header.packetBase ≤ addr ∧ addr<a.cube.cellBank) ∨
    (a.cube.stop ≤ addr ∧ addr<CubeConstants.arenaEnd a.cube.stop a.id) := by
  let f := a.lookupFrame ((CubeVisits.teamList A.axis a.cube.header.blocks owner team).length)
  let scan := a.cube.scanner (pub 0).val team A.axis.val a.cube.rowSelectorBits
  have cap := CubeAllocation.team_count a.cube A.axis owner team
  exact CubeAllocation.read_location_numbered a.cube a.id a.id f a.after.ids rfl A packet cap
    (CubeTriple.visits (l:=scan) A owner) (fun i => ⟨((CubeVisits.teamList A.axis a.cube.header.blocks owner team).get i).1,rfl⟩)
    demand pub read

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI

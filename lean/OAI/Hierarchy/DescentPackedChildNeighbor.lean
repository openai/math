import OAI.Hierarchy.DescentPackedChildNeighborMachine
import OAI.Hierarchy.DescentPackedParentFilter
import OAI.Hierarchy.DescentIssuedHostRoster
import OAI.Hierarchy.DescentFullHostOrdinal
import OAI.Hierarchy.DescentStaticWordColumn

namespace OAI
/-! The measured eight-hop parent ticket resolves through the physical successor roster. -/
namespace Hierarchy.DescentPackedChildNeighbor
open DescentHaloWalkRAM DescentParallelBase.ParentFilter DescentSIMDLookup DescentPackedColony
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {H L Q D w : ℕ}

/-- Both directions use the identical table at their own normalized receiver. -/
theorem filter_peer {E : ℕ} (adj : Fin H→Fin E→Option (Fin H))
    (roster : Fin (H*Q)→Fin D→Option (Fin (H*Q))) (v prior other : Fin H) (mine : Fin Q)
    (p : Fin (breadth E)) (dst : Endpoint (breadth E) Q) (j : Fin D) (before : Gather.reaching adj v p=some prior)
    (after : Gather.reaching adj prior dst.path=some other) (neighbor : roster (host v mine) j=some (host other dst.low))
    (unique : ∀l,roster (host v mine) l=some (host other dst.low)→l=j) :
    value (PairRanks.combined (Gather.reaching adj)) roster ((v,mine),finProdFinEquiv.symm (peer adj v p dst))=j.val := by
  simp only [peer,Equiv.symm_apply_apply]
  exact value_at _ roster v other mine dst.low (PairRanks.pair p dst.path) j (by simp [before,after]) neighbor unique

end
end Hierarchy.DescentPackedChildNeighbor

end OAI

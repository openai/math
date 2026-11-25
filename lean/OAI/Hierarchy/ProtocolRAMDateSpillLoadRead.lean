import OAI.Hierarchy.ProtocolRAMDateSpillRank
import OAI.Hierarchy.ProtocolRAMDateSpillPage
import OAI.Hierarchy.ProbeRouteOccurrences

namespace OAI
/-! # Decoding the ranked occurrence counter as the full original commodity route load -/
noncomputable section
namespace Hierarchy.ProtocolRAMDateSpillRank
open ProtocolRAM ProtocolRAM.Calendar ProtocolRAM.Calendar.CoreRoute ProtocolRAM.RouteSettlement
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard
open scoped Classical BigOperators Fin.CommRing
variable {W h d k K edges : ℕ} {S : PurchaseSampler} {π : Equiv.Perm (Fin (2^h))}
    {place : Site h d k→Fin K} (B : Mount (S:=S) π place edges) (o : Orders h d k)

/-- The ranked counters are physical RAM words. This result retains the full
number of coincident occurrences on the same wire. -/
theorem read_load (region : DateSpill.Page) (m final : Memory W)
    (eqEdges : region.edges=edges) (eqCore : region.core=coreCount o)
    (receipt : RankRead B o region.rankStart region.overflow m final)
    (word : edges≤2^W)
    (room : ∀e,routeLoad B.ordinary (fun i=>actual region.overflow m (PurchaseInventory.slot i)) e<2^W)
    (e : Fin edges) :
    (region.load.read final (e.val:Word W)).val=
      routeLoad B.ordinary (fun i=>actual region.overflow m (PurchaseInventory.slot i)) e := by
  have limit : e.val<region.load.size:=e.isLt.trans_le (eqEdges.ge.trans region.load_room)
  have addr : region.load.read final (e.val:Word W)=final (region.load.base+e.val):=by
    simp only [Bank.read,Fin.val_cast_of_lt (e.isLt.trans_le word),Nat.mod_eq_of_lt limit]
  have atCount:=RankRead.total_routeLoad B o receipt e
  have base : region.load.base=ProtocolRAMTurnReplayed.counters region.rankStart (edges+coreCount o):=by
    change ProtocolRAMTurnReplayed.counters region.rankStart (region.edges+region.core)=_
    rw [eqEdges,eqCore]
  rw [addr,base,atCount,Fin.val_cast_of_lt (room e)]

end Hierarchy.ProtocolRAMDateSpillRank
end

end OAI

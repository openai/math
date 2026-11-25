import OAI.Hierarchy.DescentNamedRootReindex
import OAI.Hierarchy.DescentResetPeerRootPages

namespace OAI
namespace Hierarchy.DescentFallbackPeriod.Projected.Receiver.IndexedRoots

/-- The address read from the physical public book survives reindexing every chart dimension. -/
theorem privatePage_reindex {D cap N n r c H G K R M hm lb tiny field Ht w D' cap' n' r' c' H' G' Ht' : ℕ}
    (x : IndexedRoots D cap N n r c H G K R M hm lb tiny field Ht w)
    (degree : D=D') (capacity : cap=cap') (dimension : n=n') (residual : r=r')
    (depth : c=c') (hosts : H=H') (groups : G=G') (height : Ht=Ht')
    (s : Bool) (t : PrivateTicket r n) (u : PrivateTicket r' n') (same : HEq u t) :
    let y:=x.reindex degree capacity dimension residual depth hosts groups height
    x.receiver.privatePageBank x.book s t=y.receiver.privatePageBank y.book s u :=by
  cases degree
  cases capacity
  cases dimension
  cases residual
  cases depth
  cases hosts
  cases groups
  cases height
  exact congrArg (x.receiver.privatePageBank x.book s) (eq_of_heq same).symm

end Hierarchy.DescentFallbackPeriod.Projected.Receiver.IndexedRoots

end OAI

import OAI.Hierarchy.DescentNamedRootReindex
import OAI.Hierarchy.DescentRootOperandRoom

namespace OAI
namespace Hierarchy.DescentFallbackPeriod.Projected.Receiver

namespace IndexedRoots
variable {D cap N n r c H G K R M hm lb tiny field Ht w : ℕ}
  {D' cap' n' r' c' H' G' Ht' : ℕ}
variable (x : IndexedRoots D cap N n r c H G K R M hm lb tiny field Ht w)
  (degree : D=D') (capacity : cap=cap') (dimension : n=n') (residual : r=r')
  (depth : c=c') (hosts : H=H') (groups : G=G') (height : Ht=Ht')


/-- Root preparation traverses the same physical addresses after dimension transport. -/
theorem unchanged (m : Computability.VPVNP.BurstRAM.Memory w) :
    let y:=x.reindex degree capacity dimension residual depth hosts groups height
    y.receiver.origin=x.receiver.origin ∧ y.receiver.saved=x.receiver.saved ∧ y.receiver.stencil=x.receiver.stencil ∧
    y.receiver.headerEnd y.book=x.receiver.headerEnd x.book ∧
    y.receiver.preparedMid y.book y.prepared m=x.receiver.preparedMid x.book x.prepared m ∧
    y.receiver.preparedImage y.book y.prepared m=x.receiver.preparedImage x.book x.prepared m :=by
  subst_vars
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- A previously checked operand region stays within the same numerical header bound. -/
theorem room_at (roof : ℕ) (area : x.sources.OperandRoom H (2^c) M w roof) :
    let y:=x.reindex degree capacity dimension residual depth hosts groups height
    y.sources.OperandRoom H' (2^c') M w roof :=by
  subst_vars
  exact area

end IndexedRoots
end Hierarchy.DescentFallbackPeriod.Projected.Receiver

end OAI

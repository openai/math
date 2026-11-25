import OAI.Hierarchy.DescentVenueSlabPhase
import OAI.Hierarchy.DescentStageVenueChange

namespace OAI
/-! # Unconditional wire-bank sizes in the public successor venue -/

namespace Hierarchy.DescentSixParty.StageVenueTail.Date
open DescentSIMDLookup DescentColonies ProtocolRAM
noncomputable section
theorem wire_room (d:Date)(B:Sources)(base w:ℕ)(x:Block d.k)(j:Fin (2*d.cap))
    (fit:d.endAddress base<2^w):
    ((d.operands B base).wire x.val j.val).Fits w (d.endAddress base) ∧
    d.hosts*chunks d.groups d.lanes≤((d.operands B base).wire x.val j.val).size:=by
  let idx:Fin d.signedShape.pages:=finProdFinEquiv (x,j)
  have ij:idx.val=x.val*(2*d.cap)+j.val:=by simp [idx,finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm]
  obtain ⟨_,lo,mid,hi⟩:=d.order base
  have end₀: d.firstEnd base≤d.endAddress base:=lo.trans (mid.trans hi)
  obtain ⟨mem,cap⟩:=DescentVenueSlabs.page_room d.signedShape base w idx (end₀.trans_lt fit)
  rw [ij] at mem cap
  exact ⟨⟨mem.1,mem.2.1,mem.2.2.trans end₀⟩,cap⟩

end
end Hierarchy.DescentSixParty.StageVenueTail.Date

end OAI

import OAI.Hierarchy.ProtocolRAMTurnGeometry
import OAI.Hierarchy.ProtocolRAMHalfRole

namespace OAI
/-! # The turn header covers precisely existing rows and existing route boundaries -/

namespace Hierarchy.ProtocolRAMTurnSpace

open ProbeStage AdaptiveProbe WireTelescope ProtocolRAM.Calendar CoreRoute
open ProtocolRAMTurnGeometry ProtocolRAMSupergroupDirectory
open scoped BigOperators Classical

theorem count {n edges h d k : ℕ} (items : Fin n ≃ ProtocolRAMTurnGeometry.Source edges h d k) :
    ProtocolRAMTurnOrder.turns (ProtocolRAMTurnGeometry.length ∘ items)=
      (edges+Fintype.card (Slots h d k))+n := by
  rw [ProtocolRAMTurnOrder.turns_eq]
  apply congrArg (·+n)
  rw [show (∑i,(ProtocolRAMTurnGeometry.length ∘ items) i)=∑s,ProtocolRAMTurnGeometry.length s from
    items.sum_comp ProtocolRAMTurnGeometry.length]
  simp [ProtocolRAMTurnGeometry.Source,SettledMatrix.Source,ProtocolRAMTurnGeometry.length,
    Fintype.sum_sum_type,Slots,Fintype.card_sigma,arity,Nat.add_assoc]

theorem space (N roles sites seats : ℕ) :
    6*span N+span (2*roles)+(1+3*N)+7*N+5*(sites*seats)+10*N ≤
      32*N+4*roles+5*(sites*seats)+15 := by
  have hn := ProtocolRAMSupergroupDirectory.space N
  have hr := ProtocolRAMHalfRole.space_le roles
  omega

end Hierarchy.ProtocolRAMTurnSpace

end OAI

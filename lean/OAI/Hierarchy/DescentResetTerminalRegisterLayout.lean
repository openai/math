import OAI.Hierarchy.DescentDatedResetOutput
import OAI.Hierarchy.DescentRegisterTypes
import OAI.Hierarchy.DescentResetRegisterExtent

namespace OAI
/-! # Reset output banks in the prior operand and role registers -/

namespace Hierarchy.DescentDatedAddressBook
noncomputable section

namespace ResetOutput

variable (v : ResetOutput) (base : ℕ)

def terminalField (f : Fin 7) (j : Fin v.argumentSlots) (x : Fin v.receiver.blocks) : ProtocolRAM.Bank :=
  DescentResetNodeBooks.bank (v.scalarEnd base) v.nodeNames v.nodes v.receiver.hosts v.receiver.groups v.nodeBits v.receiver.lanes
    (finProdFinEquiv (DescentOperandStateBanks.page f j,x))

def terminalPointers (f : Fin 4) := v.terminalField base (f.castLE (by decide))

theorem terminal_order : v.finalEnd base≤v.fullEnd base ∧ v.fullEnd base≤v.primitiveEnd base ∧
    v.primitiveEnd base≤v.metadataEnd base := by
  refine ⟨(v.complete_after base).1.trans (v.complete_after base).2,?_,?_⟩
  · change v.fullEnd base≤v.primitive.endAddress (v.birth.endAddress (v.actorClass.endAddress
      (v.roleTransfer.endAddress (v.fullEnd base))))
    rw [v.primitive.translate,v.birth.translate,v.actorClass.translate,v.roleTransfer.translate]
    omega
  · change v.primitiveEnd base≤v.metadata.endAddress (v.primitiveEnd base)
    rw [v.metadata.translate]
    omega

theorem terminal_field_room {w : ℕ} (space : v.metadataEnd base<2^w) (f : Fin 7) (j : Fin v.argumentSlots)
    (x : Fin v.receiver.blocks) :
    (v.terminalField base f j x).Fits w (v.finalEnd base) ∧
      v.receiver.hosts*DescentSIMDLookup.chunks v.receiver.groups v.receiver.lanes ≤ (v.terminalField base f j x).size := by
  have o:=v.terminal_order base
  exact DescentResetNodeBooks.register_room v.rangeLayout (v.scalarEnd base) v.nodeBits w
    (DescentOperandStateBanks.page f j) x ((o.1.trans (o.2.1.trans o.2.2)).trans_lt space)

end ResetOutput

namespace PriorRolePages

def reset (v : ResetOutput) (base : ℕ) : PriorRolePages:=
  let p:=v.primitive
  ⟨p.out (v.birthEnd base),p.chart.rows,Nat.clog 2 (p.chart.rows+1),p.chart.blocks⟩

end PriorRolePages

namespace PriorResetArchive

def reset (v : ResetOutput) (base : ℕ) : PriorResetArchive:=
  ⟨v.metadata.headerEnd (v.primitiveEnd base),
    DescentResetNodeBooks.output (v.scalarEnd base) v.nodeNames v.nodes v.receiver.hosts
      v.receiver.groups v.nodeBits v.receiver.lanes,false,PriorRolePages.reset v base,
    (v.actor.directory (v.middle.stop base)).count⟩

end PriorResetArchive

namespace ResetOutput

/-- The archived operand directory ends at the last allocated reset node book. -/
theorem terminal_previous_limit (v : ResetOutput) (base : ℕ) :
    v.rangeLayout.previousLimit (PriorResetArchive.reset v base).arguments = v.finalEnd base :=
  DescentResetNodeBooks.previous_limit v.rangeLayout (v.scalarEnd base) v.nodeBits

end ResetOutput

end
end Hierarchy.DescentDatedAddressBook

end OAI

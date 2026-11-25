import OAI.Hierarchy.DescentResetTerminalRegisterLayout
import OAI.Hierarchy.DescentMountedResetRegister

namespace OAI
/-! # The four pointer header fields in the mounted reset register -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentSIMDLookup DescentDatedPriorOperand
noncomputable section

theorem terminal_header_bank (v : ResetOutput) (base : ℕ) (x : Fin v.receiver.blocks)
    (j : Fin v.argumentSlots) (f : Fin 4) :
    previousBank v.rangeLayout (PriorResetArchive.reset v base).arguments x (DescentOperandStateBanks.page (f.castLE (by decide : 4≤7)) j)=
      v.terminalField base (f.castLE (by decide : 4≤7)) j x := by
  exact DescentResetNodeBooks.previous_bank v.rangeLayout (v.scalarEnd base) v.nodeBits
    (DescentOperandStateBanks.page (f.castLE (by decide : 4≤7)) j) x

/-- Physical capture and mounting preserve the four pointer addresses referenced
by ordinary host ordinals in the final one-chunk layout. -/
theorem header_after_mount (v : ResetOutput) {w : ℕ} (base captured size : ℕ) (source : ℕ→ℕ)
    {roleBase replayBase : ℕ} (rom : DescentSixParty.Chronology.RoleMount w roleBase replayBase)
    (m : Computability.VPVNP.BurstRAM.Memory w) (early : captured+size≤base)
    (done_ : v.finalEnd base≤roleBase) (_space : v.metadataEnd base<2^w)
    (one : chunks v.receiver.groups v.receiver.lanes=1)
    (f : Fin 4) (j : Fin v.argumentSlots) (x : Fin v.receiver.blocks) (h : Fin v.receiver.hosts) :
    rom.phase.image (DescentLowCountBook.output captured source m size)
      ((v.terminalField base (f.castLE (by decide)) j x).base+h.val)=
      m ((previousBank v.rangeLayout (PriorResetArchive.reset v base).arguments x
        (DescentOperandStateBanks.page (f.castLE (by decide : 4≤7)) j)).base+h.val) := by
  have scalarStart : base ≤ v.scalarEnd base := by
    change base ≤ v.endAddress base
    rw [v.translated base]
    exact Nat.le_add_right ..
  exact DescentResetNodeBooks.header_after_mount v.rangeLayout (v.scalarEnd base) v.nodeBits captured size
    source rom m (early.trans scalarStart) done_ one (f.castLE (by decide : 4≤7)) j x h

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI

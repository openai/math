import OAI.Hierarchy.DescentPhysicalMixedCapture

namespace OAI
/-! # The earlier compact-directory registers at the native rank-port entry -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs
open DescentSixParty.Chronology DescentSIMDLookup DescentResetFieldAssembler
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
variable {a : PhysicalReset} {floor w : ℕ} (u : a.DateInputs floor w)

def before_ports (ok : u.Ready) (actorMem : Memory w) : Memory w :=
  let v:=a.successor
  let b:=a.rebased floor
  DescentResetCandidatePair.memory (v.sheetsStart b) u.sectors.pageBits v.receiver.hosts
    v.receiver.groups v.receiver.lanes u.sectors.header u.sectors.original (u.sheetsEntry ok actorMem)

theorem before_ports_frame (ok : u.Ready) (actorMem : Memory w) (j : ℕ)
    (below : j< a.successor.massEnd (a.rebased floor)) :
    u.before_ports ok actorMem j=u.contactResult actorMem j := by
  let v:=a.successor
  let b:=a.rebased floor
  let s:=v.sheets
  let r:=(v.remap b).endAddress
  let co:=u.privateResult actorMem
  let mixed:=u.masked.image co
  let out:=u.sheetsEntry ok actorMem
  have ordered:=v.receipt_order b
  have privateLow : j< v.jointEnd b:=below.trans_le ordered.1
  have mixedLow : j< u.masked.first:=privateLow.trans_le ordered.2
  have numberedLow : j< s.metaEnd r:=by
    rw [←u.masks_end]
    exact mixedLow.trans_le (u.masked.ordered.1.trans u.masked.ordered.2)
  have pairedLow : j< v.sheetsStart b:=by
    have order:=ok.ordered
    rcases order with ⟨_,_,_,_,h₁,h₂,h₃,h₄,_⟩
    exact below.trans_le (((h₁.trans h₂).trans h₃).trans h₄)
  have room : DescentResetCandidatePair.endAddress (v.sheetsStart b) v.receiver.blocks
      (CandidateSheet.size u.sectors.stems u.sectors.contacts u.sectors.privates) u.sectors.pageBits < 2^w := by
    rw [ok.matched]
    exact (v.rankPort_after b).trans_lt ok.rankPorts.limit
  have paired:=DescentResetCandidatePair.any (v.sheetsStart b) u.sectors.pageBits v.receiver.hosts
    v.receiver.groups v.receiver.lanes u.sectors.header u.sectors.original out ok.header ok.original ok.rows room
  have numbered:=u.numbered.any r mixed ok.numbers
  have masks:=u.masked.any co (u.genuine_mask_previous ok.joints ok.masked) ok.masked
  have fits:=v.private_inputs_fit b u.earlier ok.pages ok.privates
  have points:=v.private_any b u.earlier (u.privateStart actorMem)
    ok.projectionLanes ok.projectionBlocks fits ok.privates
  have joined:=v.joint_any b u.earlier (u.contactResult actorMem) ok.joints ok.packed
  exact (paired.2.1 j (.inl pairedLow)).trans ((numbered.2.2 j (.inl numberedLow)).trans
    ((masks.2.2 j (.inl mixedLow)).trans ((points.2 j (.inl privateLow)).trans (joined.2 j (.inl below)))))

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs

end OAI

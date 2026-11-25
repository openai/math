import OAI.Hierarchy.DescentCanonicalFrontSources
import OAI.Hierarchy.DescentPreparedSenderPrior
import OAI.Hierarchy.DescentResetPeerRootPages
import OAI.Hierarchy.DescentResetActorDirectoryCode

namespace OAI
/-! # Original physical operands of the dated peer, contact and stem scans -/
namespace Hierarchy.DescentDatedAddressBook.CandidateFront.EarlierBanks
open DescentFallbackPeriod DescentFallbackPeriod.Projected DescentResetGates DescentPackedColony DescentSIMDLookup
open DescentResetHostSize DescentSharedBookScan DescentDenseHostOrder DescentSixParty.Chronology
open ThreeFlat.RAM PhysicalProcedure ProtocolRAM
noncomputable section
set_option quotPrecheck false
variable {D cap N n r c H G K R M h l t field Ht w : ℕ}
  (a : Receiver D cap N n r c H G K R M h l t field Ht w)
  (b : RootBook n r D (2^r) cap field)
  (original : RootSources D (2^r) cap) (oldId oldHub : Bank)
  (dir : DescentResetNewActorDirectory.Layout) (scene : Bank)

def rankTicket (r n : ℕ) : Code r×Option (Fin (2^n)) := (⟨(0,0),DescentHostDirectory.mem_codes (Nat.zero_le _) (by decide)⟩,none)

/-- Every field is an address in the executed root, original roster, or actor directory. -/
def fromRoot : EarlierBanks D r cap n where
  ports:=original.peers
  window:=bankAt a.stencil a.tapped t D a.signedEnd H (2^c) M
  roots:=a.privatePageBank b
  actorStarts:=dir.roots
  actorData:=scene
  oldRoster:=original.peers.roster
  oldHub:=oldHub
  donor:=original.senderPrior H n r oldId (b.rankHeader a.projectionEnd H (2^c) M (false,.inr (rankTicket r n)))

theorem from_root_inputs :
    let old:=fromRoot a b original oldId oldHub dir scene
    old.actorStarts=dir.roots ∧ old.actorData=scene ∧ old.oldRoster=original.peers.roster ∧
      (∀s j,old.roots s j=a.privatePageBank b s j) ∧ old.donor.routes=original.peers :=
  ⟨rfl,rfl,rfl,fun _ _=>rfl,rfl⟩

end
end Hierarchy.DescentDatedAddressBook.CandidateFront.EarlierBanks

end OAI

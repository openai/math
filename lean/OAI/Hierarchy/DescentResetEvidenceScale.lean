import OAI.Hierarchy.DescentResetEvidenceTraffic
import OAI.Hierarchy.DescentNamedFrontWords
import OAI.Hierarchy.DescentResetReceiverPitch

namespace OAI
/-! The actual raw-evidence and peer stages read each live host or packed group a
locally bounded number of times. Their private lookup ROMs are shared across all rows. -/
namespace Hierarchy.DescentDatedAddressBook
namespace CandidateFront
open DescentSIMDLookup DescentResetPeerUnionRAM
noncomputable section

def evidenceFactor (D slots shapes cap limit : ℕ) :=
  evidenceCost D slots shapes cap limit 1 1 1

def peerFactor (D shapes E limit : ℕ) := peerCost D shapes E limit 1 1 1 1

theorem evidence_linear (D slots shapes cap limit H rows T shared : ℕ)
    (h : H ≤ T) (r : rows ≤ T) (s : shared ≤ T) (pos : 0 < T) :
    evidenceCost D slots shapes cap limit H rows shared ≤ evidenceFactor D slots shapes cap limit*T := by
  have up:evidenceCost D slots shapes cap limit H rows shared ≤ evidenceCost D slots shapes cap limit T T T := by
    unfold evidenceCost
    dsimp only
    gcongr
  apply up.trans
  obtain ⟨k,eq⟩:=Nat.exists_eq_add_of_le (show 1 ≤ T by omega)
  rw [eq]
  unfold evidenceFactor evidenceCost
  dsimp only
  ring_nf
  omega

theorem peer_linear (D shapes E limit H rows newRows T shared : ℕ)
    (h : H ≤ T) (r : rows ≤ T) (next : newRows ≤ T) (s : shared ≤ T) (pos : 0 < T) :
    peerCost D shapes E limit H rows newRows shared ≤ peerFactor D shapes E limit*T := by
  have up : peerCost D shapes E limit H rows newRows shared ≤ peerCost D shapes E limit T T T T := by
    unfold peerCost
    dsimp only
    gcongr
  apply up.trans
  obtain ⟨k,eq⟩:=Nat.exists_eq_add_of_le (show 1 ≤ T by omega)
  rw [eq]
  unfold peerFactor peerCost
  dsimp only
  ring_nf
  omega

variable (v : CandidateFront)

def evidenceTrafficFactor (U : ℕ) :=
  evidenceFactor v.peer.oldDegree v.oldKeysCount v.peer.shapes v.wireCap U+
  peerFactor v.peer.oldDegree v.peer.shapes v.peer.evidence U

/-- The traffic bound is on actual padded tables. A host with no active route is
still covered by the count of public hosts and by the public instruction text. -/
theorem evidence_scale (floor U h T : ℕ) (host : 0 < v.peer.oldHosts)
    (hosts : v.peer.oldHosts ≤ T) (oldRows : v.peer.oldHosts*chunks v.oldGroups v.oldLanes ≤ T)
    (peerRows : v.peer.oldHosts*chunks v.peer.evidenceGroups v.peer.evidenceLanes ≤ T)
    (newRows : v.peer.hosts*chunks v.peer.groups v.peer.lanes ≤ T) (shared : 2^(h/2) ≤ T)
    (key : DescentResetStemKey.unit v.peer.oldDegree v.stemField*v.oldLanes ≤ h/2)
    (privateKey : (v.privateBits*(v.wireCap*5))*v.oldLanes ≤ h/2)
    (stems : (v.stemField+2)*v.oldLanes ≤ h/2) (trunk : v.oldLanes ≤ h/2)
    (peerKey : v.peer.bits*v.peer.evidenceLanes ≤ h/2) :
    v.oldEvidenceBill floor U+v.peerBill U ≤ v.evidenceTrafficFactor U*T := by
  have pos:T>0:=(Nat.two_pow_pos (h/2)).trans_le shared
  have early:=(v.evidence_traffic floor U h key privateKey stems trunk).trans
    (evidence_linear _ _ _ _ _ _ _ _ _ hosts oldRows shared pos)
  have peer:=(v.peer_traffic U h host peerKey).trans
    (peer_linear _ _ _ _ _ _ _ _ _ hosts peerRows newRows shared pos)
  simpa only [evidenceTrafficFactor,Nat.add_mul] using Nat.add_le_add early peer

end
end CandidateFront
namespace ResetOutput
/-- Five relevant retained keys from the genuine selected receiver. -/
theorem evidence_keys (v : ResetOutput) (old : v.front.oldLanes=v.receiver.lanes)
    (peer : v.front.peer.evidenceLanes=v.receiver.lanes) (degree : v.front.peer.oldDegree=v.middle.rootDegree)
    (h : ℕ) (room : ∀ x ∈ v.rootUnits,x*v.receiver.lanes ≤ h/2) :
    DescentResetStemKey.unit v.front.peer.oldDegree v.front.stemField*v.front.oldLanes ≤ h/2 ∧
    (v.front.privateBits*(v.front.wireCap*5))*v.front.oldLanes ≤ h/2 ∧
    (v.front.stemField+2)*v.front.oldLanes ≤ h/2 ∧
    v.front.oldLanes ≤ h/2 ∧ v.front.peer.bits*v.front.peer.evidenceLanes ≤ h/2 := by
  rw [old,peer,degree]
  have stem:=room (v.front.stemField+2) (by simp [rootUnits])
  have lanes:=Nat.le_mul_of_pos_left v.receiver.lanes (show 0 < v.front.stemField+2 by omega)
  exact ⟨room _ (by simp [rootUnits]),room _ (by simp [rootUnits]),stem,lanes.trans stem,room _ (by simp [rootUnits])⟩
end ResetOutput
end Hierarchy.DescentDatedAddressBook

end OAI

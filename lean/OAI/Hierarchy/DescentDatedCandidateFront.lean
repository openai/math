import OAI.Hierarchy.DescentContactDonorShape
import OAI.Hierarchy.DescentResetTrunkCompactProgram
import OAI.Hierarchy.DescentContactPreROMBounds
import OAI.Hierarchy.DescentDatedCandidateOrigin
import OAI.Hierarchy.DescentResetParentAperture
import OAI.Hierarchy.DescentResetPrivatePeerChip
import OAI.Hierarchy.DescentResetStemPeerChip
import OAI.Hierarchy.DescentResetStemArenaPlan
import OAI.Hierarchy.DescentResetStemProjectRate
import OAI.Hierarchy.DescentResetTrunkIssue

namespace OAI
/-! # The measured predecessor bank and both stages of stem reception in a reset date -/
namespace Hierarchy.DescentDatedAddressBook
open DescentSIMDLookup DescentDyadicSpan DescentResetStemPackedIssue DescentResetPeerUnionRAM
open DescentResetStemKey Filter ProtocolRAM
noncomputable section

structure CandidateFront where
  peer : PeerAperture
  donor : DescentContactDonorFront.Shape
  contact : DescentContactPreROM.Layout
  oldGroups : ℕ
  oldLanes : ℕ
  oldKeysCount : ℕ
  wireCap : ℕ
  privateBits : ℕ
  stemField : ℕ
  metaBits : ℕ
  oldTicketCount : ℕ
  signedQueries : ℕ
  projectionCount : ℕ
  projectionBits : ℕ
  blocks : ℕ
  newHosts : ℕ

namespace CandidateFront
variable (v : CandidateFront)

def oldKeys (base : ℕ) :=Columns.stop base v.peer.oldDegree v.stemField v.oldLanes v.peer.oldHosts v.oldGroups v.oldKeysCount

def privateChip (base : ℕ) :=PrivateEvidence.endAddress (v.oldKeys base) v.peer.oldHosts v.peer.shapes v.wireCap v.privateBits v.oldLanes

def positiveStem (base : ℕ) :=DescentResetStemPeerChip.endAddress v.peer.shapes (v.privateChip base) v.peer.oldHosts (v.stemField+2) v.oldLanes

def negativeStem (base : ℕ) :=DescentResetStemPeerChip.endAddress v.peer.shapes (v.positiveStem base) v.peer.oldHosts (v.stemField+2) v.oldLanes

def rawTablesEnd (base : ℕ) :=v.peer.chipEnd (v.negativeStem base)

def donorStart (base : ℕ) :=v.rawTablesEnd base
def donorEnd (base : ℕ) :=v.donor.endAddress (v.donorStart base)

def contacts (base : ℕ) :=({v.contact with first:=v.donorEnd base} : DescentContactPreROM.Layout).endAddress

def peers (base : ℕ) :=v.contacts base

def parentStart (base : ℕ) :=v.peer.endAddress (v.peers base)+v.newHosts

def parentEnd (base : ℕ) :=DescentResetParentAperture.endAddress (v.parentStart base) v.peer.hosts v.newHosts

def parent (base : ℕ) : Bank :=DescentResetParentAperture.parent (v.parentStart base) v.peer.hosts v.newHosts

def projected (base : ℕ) :=DescentResetStemProject.endAddress (v.parentEnd base) v.projectionCount v.peer.oldHosts
  v.peer.groups v.blocks v.projectionBits v.oldLanes v.peer.lanes

def mixed (base : ℕ) :=Mixed.endAddress (v.projected base) (v.parent base).base v.peer.oldDegree v.stemField v.metaBits
  v.oldTicketCount v.peer.oldHosts v.newHosts v.peer.groups v.peer.lanes v.blocks v.signedQueries

def gathered (base : ℕ) :=DescentResetTrunkCompactGather.endAddress (v.mixed base) v.newHosts v.peer.groups v.peer.lanes

def trunkEnd (base : ℕ) :=DescentResetTrunkIssue.endAddress (v.gathered base) v.metaBits v.peer.lanes

theorem negative_shift (base : ℕ) : v.negativeStem base=base+v.negativeStem 0 := by
  simp only [negativeStem,positiveStem,privateChip,oldKeys,Columns.stop,Columns.start,
    PrivateEvidence.endAddress,DescentResetStemPeerChip.endAddress,DescentResetStemPeerChip.start,
    Nat.zero_add,Nat.add_assoc]

theorem trunk_shift (base : ℕ) : v.trunkEnd base=base+v.trunkEnd 0 := by
  have t (s : ℕ) : v.rawTablesEnd s=s+v.rawTablesEnd 0 := by
    simp only [rawTablesEnd,PeerAperture.chipEnd,v.negative_shift s,Nat.add_assoc]
  have c (s : ℕ) : v.peers s=s+v.peers 0 := by
    unfold peers contacts
    unfold donorEnd donorStart
    rw [v.contact.translate,v.contact.translate (v.donor.endAddress (v.rawTablesEnd 0)),
      v.donor.translate (v.rawTablesEnd s),v.donor.translate (v.rawTablesEnd 0),t s]
    omega
  have p (s : ℕ) : v.parentStart s=s+v.parentStart 0 := by
    unfold parentStart
    rw [v.peer.extent (v.peers s), v.peer.extent (v.peers 0), c s]
    omega
  have q (s : ℕ) : v.parentEnd s=s+v.parentEnd 0 := by
    unfold parentEnd
    rw [DescentResetParentAperture.affine (v.parentStart s),DescentResetParentAperture.affine (v.parentStart 0),p s,Nat.add_assoc]
  have z (s : ℕ) : v.projected s=s+v.projected 0 := by
    unfold projected
    rw [DescentResetStemProject.extent (v.parentEnd s),DescentResetStemProject.extent (v.parentEnd 0),q s,Nat.add_assoc]
  unfold trunkEnd gathered mixed
  simp only [
    DescentResetTrunkIssue.endAddress,DescentResetTrunkCompactGather.endAddress,DescentResetTrunkCompactGather.geometry,
    DescentResetTrunkCompactRows.endAddress,DescentResetTrunkCompactRows.rowBase]
  rw [Mixed.affine (v.projected base), Mixed.affine (v.projected 0), z base]
  omega

end CandidateFront
end
end Hierarchy.DescentDatedAddressBook

end OAI

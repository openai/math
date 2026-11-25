import OAI.Hierarchy.DescentResetReceivedEvidencePrice

namespace OAI
/-! Host and packed-group traffic of the actual installed private, stem, trunk and
raw candidate evidence. The padded lookup pages are shared by all hosts. -/
namespace Hierarchy.DescentDatedAddressBook.CandidateFront
open DescentSIMDLookup DescentDyadicSpan DescentResetStemKey DescentResetStemPackedIssue
open DescentResetPeerUnionRAM
noncomputable section
variable (v : CandidateFront)

def evidenceCost (D slots shapes cap limit H rows shared : ℕ) :=
  let book:=((D+2)+2)*(2*shared)
  let score:=14+(D+2)*(limit+11)
  let bucket:=2*(H*shapes)+1
  let lookup:=2*(shapes*shared)+1
  let pages:=2*bucket+cap*lookup+2*(bucket+lookup)+(bucket+lookup)
  (4+10*book)+(4+slots*(4+rows*(2*score+4)))+
    7*(15*(book+1)+(15+slots*(11+4*score)))+
    (16+10*pages)+7*(15*(pages+4))

theorem evidence_tables (v : CandidateFront) (floor shared : ℕ)
    (privateKey : 2^((v.privateBits*(v.wireCap*5))*v.oldLanes) ≤ shared)
    (stems : 2^((v.stemField+2)*v.oldLanes) ≤ shared) (trunk : 2^v.oldLanes ≤ shared) :
    (v.rawTables floor).words ≤
      let cells:=2*(v.peer.oldHosts*v.peer.shapes)+1
      let entries:=2*(v.peer.shapes*shared)+1
      2*cells+v.wireCap*entries+2*(cells+entries)+(cells+entries) := by
  let S:=v.peer.shapes
  let H:=v.peer.oldHosts
  have host:=span_le (H*S)
  have sp {n : ℕ} (le:n ≤ shared) : span (S*n) ≤ 2*(S*shared)+1 :=
    (span_le _).trans (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left S le)) 1)
  have p:=sp privateKey
  have s:=sp stems
  have t:=sp trunk
  dsimp only
  change 2*span (H*S)+v.wireCap*span (S*2^((v.privateBits*(v.wireCap*5))*v.oldLanes))+
    2*(span (H*S)+span (S*2^((v.stemField+2)*v.oldLanes)))+
    (span (H*S)+span (S*2^v.oldLanes)) ≤ _
  gcongr

theorem evidence_traffic (floor limit payload : ℕ)
    (keys : unit v.peer.oldDegree v.stemField*v.oldLanes ≤ payload/2)
    (privateKey : (v.privateBits*(v.wireCap*5))*v.oldLanes ≤ payload/2)
    (stems : (v.stemField+2)*v.oldLanes ≤ payload/2) (trunk : v.oldLanes ≤ payload/2) :
    v.oldEvidenceBill floor limit ≤
      evidenceCost v.peer.oldDegree v.oldKeysCount v.peer.shapes v.wireCap limit
        v.peer.oldHosts (v.peer.oldHosts*chunks v.oldGroups v.oldLanes) (2^(payload/2)) := by
  have key:=Nat.pow_le_pow_right (by decide : 0<2) keys
  have pages:=evidence_tables v floor (2^(payload/2)) (Nat.pow_le_pow_right (by decide) privateKey)
    (Nat.pow_le_pow_right (by decide) stems) (Nat.pow_le_pow_right (by decide) trunk)
  dsimp only at pages
  unfold oldEvidenceBill evidenceCost Mixed.keyNames DescentResetStemKey.words
  dsimp only
  gcongr

def peerCost (D shapes E limit H rows newRows shared : ℕ) :=
  let slots:=Candidates.count shapes D
  let wide:=H*shapes
  let literal:=2*(2*(wide+1))+(2*(H+1))
  let flags:=slots*E*shared
  let scan:=42*wide+(rows*shapes)*(E*(limit+8))
  let scanText:=42+rows*(E*(limit+8))
  let compute:=Program.sortWork slots
  let time:=((4+10*literal)+(4+10*flags))+
    ((4+slots*(4+(2*scan+4*wide)))+(4+3*(4+wide*(2*compute+4))))
  let text:=(15*(literal+1)+15*(flags+1))+
    ((15+slots*(11+4*scanText))+(15+3*(11+4*compute)))
  let loc:=3*(2*(wide*4)+1)
  let chart:=4*newRows+(wide+(newRows+wide*4))
  (time+((4+10*loc)+(4+10*chart)+(4+(wide*4)*84)+(4+(wide*4)*25004))+(4+10*(3*wide)))+
    7*(text+(15*(loc+1)+15*(chart+1)+171+50011)+15*(3*wide+1))

theorem peer_traffic (limit payload : ℕ) (host : 0 < v.peer.oldHosts)
    (key : v.peer.bits*v.peer.evidenceLanes ≤ payload/2) :
    v.peerBill limit ≤ peerCost v.peer.oldDegree v.peer.shapes v.peer.evidence limit v.peer.oldHosts
      (v.peer.oldHosts*chunks v.peer.evidenceGroups v.peer.evidenceLanes)
      (v.peer.hosts*chunks v.peer.groups v.peer.lanes) (2^(payload/2)) := by
  let p:=v.peer
  let H:=p.oldHosts
  let S:=p.shapes
  let K:=chunks p.evidenceGroups p.evidenceLanes
  let c:=Program.columnWork p.evidence p.evidenceGroups p.evidenceLanes limit
  have width:=Nat.pow_le_pow_right (by decide : 0<2) key
  have candidates:Candidates.length H S ≤ 2*(2*(H*S+1))+2*(H+1) :=
    Nat.add_le_add (Nat.mul_le_mul_left 2 (Overlap.rounded (H*S))) (Overlap.rounded H)
  have pad:=span_le ((H*S)*4)
  have units:K ≤ H*K:=Nat.le_mul_of_pos_left _ host
  have C:c ≤ 42+(H*K)*(p.evidence*(limit+8)) := by
    change 42+(p.evidence*K)*(limit+8) ≤ _
    rw [Nat.mul_comm p.evidence K,Nat.mul_assoc]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ units) 42
  have body:H*S*(2*c+4)=2*(42*(H*S)+(H*K*S)*(p.evidence*(limit+8)))+4*(H*S) := by
    dsimp only [c,Program.columnWork,K]
    ring
  unfold peerBill peerCost Program.timeBound Program.hardwareBound
  dsimp only
  change _ ≤ _
  dsimp only [PeerAperture.hosts,DescentScalarHaloPortROM.length,Packed.words] at *
  change DescentResetSelfPortsRAM.pad (H*S) ≤ 2*(H*S*4)+1 at pad
  change 2^(p.bits*p.evidenceLanes) ≤ _ at width
  change H*S*(2*Program.columnWork p.evidence p.evidenceGroups p.evidenceLanes limit+4)=_ at body
  dsimp only [p,H,S,K] at body candidates pad C
  rw [body]
  gcongr

end
end Hierarchy.DescentDatedAddressBook.CandidateFront

end OAI

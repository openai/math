import OAI.Hierarchy.DescentPhysicalResetEvidence
import OAI.Hierarchy.DescentResetPeerAxes
import OAI.Hierarchy.DescentResetStemIssuedWindows
import OAI.Hierarchy.DescentResetStemShapeTemplate
import OAI.Hierarchy.DescentRecordedRotorLayers
import OAI.Hierarchy.DescentPackedPrivateMenu

namespace OAI
/-! # The reset's peer probes, donors, stems and compact trunk from public calendar data -/
namespace Hierarchy.DescentDatedAddressBook.CandidateFront
open DescentSixParty DescentCompiler DescentDenseHostOrder DescentSIMDLookup DescentPackedColony
open DescentResetStemPackedIssue DescentFallbackPeriod
noncomputable section
set_option quotPrecheck false

/-- The receiver and the following date may use different lane counts. The width
of each root field and the successor's metadata width come from their physical banks. -/
def setupFront {n h : ℕ} (S : AtomSchedule) (board : NonlinearExpanders.Graph n h)
    (k tail age degree f g receiverBatch nextBatch rootField metaBits C packet : ℕ) (calendar : List ℕ) : CandidateFront :=
  let H:=S.hostSize age
  let c:=S.groupWidth k tail age
  let L:=2^k
  let cap:=(calendar.take age).prod*256
  let height:=GroupStage.depthBound degree n f g
  let shapes:=(roster board k height).card
  let evidence:=ClosedReset.Window.publicEvidenceRows board height k cap
  let markerBits:=Nat.clog 2 ((degree+1)*shapes+1)
  let keys:=count L cap
  let donor : DescentContactDonorFront.Shape:=
    ⟨H,2^c,receiverBatch,degree,L,cap,n,k,height,rootField,Nat.clog 2 (degree+2),Nat.clog 2 (degree+3)⟩
  {peer:=⟨H,shapes,degree,evidence,markerBits,2^c,receiverBatch,S.groupCount (age+1),nextBatch⟩,
   donor:=donor,contact:=⟨0,H,shapes,2^c,receiverBatch,degree,L,cap,n,k,height,rootField,markerBits⟩,
   oldGroups:=2^c,oldLanes:=receiverBatch,oldKeysCount:=keys,wireCap:=DescentResetCableSlots.cableCap board height,
   privateBits:=DescentPackedPrivateMenu.fieldBits board k height (L*(2*cap))
      (DescentRecordedRotorLayers.width f cap) C packet,stemField:=rootField,metaBits:=metaBits,
   oldTicketCount:=2*DescentFallbackShapeTable.rows k (2^n),signedQueries:=keys,
   projectionCount:=keys*(degree+2),projectionBits:=rootField,blocks:=L,newHosts:=S.hostSize (age+1)}

variable {n h : ℕ} (S : AtomSchedule) (board : NonlinearExpanders.Graph n h)
    (k tail age degree f g receiverBatch nextBatch rootField metaBits C packet : ℕ) (calendar : List ℕ)
local notation "A" => setupFront S board k tail age degree f g receiverBatch nextBatch rootField metaBits C packet calendar
local notation "L" => 2^k
local notation "height" => GroupStage.depthBound degree n f g
local notation "cap" => (calendar.take age).prod*256

/-- The shape-dependent part of the code uses the same physical incoming port
and signed-column expressions for the early key scan and later projection. -/
def setupEvidence (ports : Ports degree) (bank : Projected.Column L cap→ProtocolRAM.Bank) : (A).Evidence where
  n:=n
  oldPorts:=h
  rootBits:=k
  depth:=height
  board:=board
  decode:=DescentResetStemKey.parse degree cap rootField
  sides:=side L cap
  source:=operands ports bank (S.hostSize age)
  template s j:=DescentResetStemDecoder.localTemplate board k height s j.val

theorem setup_marker_fits :
    (degree+1)*(roster board k height).card<2^(A).peer.bits := by
  exact (Nat.lt_succ_self _).trans_le (Nat.le_pow_clog (by decide) _)

theorem setup_query_bits :
    degree+1<2^(A).donor.queryBits ∧ degree+2<2^(A).donor.cargoBits :=
  ⟨(Nat.lt_succ_self _).trans_le (Nat.le_pow_clog (by decide) _),
   (Nat.lt_succ_self _).trans_le (Nat.le_pow_clog (by decide) _)⟩

end
end Hierarchy.DescentDatedAddressBook.CandidateFront

end OAI

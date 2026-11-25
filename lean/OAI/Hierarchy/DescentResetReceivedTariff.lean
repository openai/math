import OAI.Hierarchy.DescentResetReceivedEvidencePrice
import OAI.Hierarchy.DescentContactPreROMPrice
import OAI.Hierarchy.DescentContactDonorFrontPrice

namespace OAI
/-! A single finite bill for the six native phases between the actor catalog and the trunk. -/
namespace Hierarchy.DescentDatedAddressBook.CandidateFront
open DescentSIMDLookup DescentStaticWordColumn DescentResetTrunkCompactScalar
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
set_option quotPrecheck false
variable (v : CandidateFront) (base : ℕ) (s : v.Scene) {w : ℕ} (ok : v.SceneRoom base s w)
local notation "C" => v.contactLayout base
local notation "donorStart" => v.donorStart base

/-- A uniform operand work bound concerns only the actual earlier expressions in
the compiled scene. All reads of individually published donor sensors cost seven. -/
structure OperandPrice (limit : ℕ) : Prop where
  evidence : ∀q i,(s.evidence.source q i).work ≤ limit
  donor : ∀j,(s.donor.board j).work ≤ limit
  host : s.donor.host.work ≤ limit
  ones : s.donor.ones.work ≤ limit
  contact : ∀j,(s.boardReads j).work ≤ limit
  peer : ∀j p,(s.peers.src j p).work ≤ limit
  raw : s.rawHeader.work ≤ limit
  stems : ∀q j,(s.stems.operands q j).work ≤ limit
  ports : s.stems.ports.All (fun e=>e.work ≤ limit)

def receivedBill (limit : ℕ) :=
  let old:=(C).oldLimit limit
  let marker:=DescentContactPreROM.Layout.markerLimit 7
  let scalar:=8*limit+10
  v.oldEvidenceBill base limit+
    (v.donor.fee donorStart limit+7*v.donor.size donorStart limit)+
    ((C).clockBound old marker+7*(C).size old marker)+v.peerBill limit+
    (4+v.newHosts*(2*scalar+4)+7*(11+4*scalar))+v.stemBill limit limit

theorem received_price (limit : ℕ) (operands : v.OperandPrice s limit) (old : 0 < v.oldLanes) :
    (v.received base s ok).ticks+7*names (v.received base s ok).program ≤ v.receivedBill base limit := by
  have earlier:=v.oldEvidence_price base s ok limit operands.evidence
  have donor:=v.donor.priced (w:=w) donorStart s.donor limit operands.donor operands.host operands.ones
  have bought:=(C).reads_priced s.rotor s.boardReads (v.sensor base s) ok.contact limit 7 operands.contact
    (fun _ _ _=>le_rfl)
  have peer:=v.peer_price base s ok limit operands.peer
  have projected:=v.stem_price base s ok limit limit operands.stems operands.ports old
  let scalar:=tested s.count s.inverse s.rawHeader
  have cpu : scalar.work≤8*limit+10 := (cost s.count s.inverse s.rawHeader).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left 8 operands.raw) _)
  have scans:=Nat.mul_le_mul_left v.newHosts (Nat.add_le_add_right (Nat.mul_le_mul_left 2 cpu) 4)
  have text:=Nat.mul_le_mul_left 4 cpu
  have scalarNames:names (v.scalarPhase base s w).program=11+4*scalar.work:=names_scan ..
  change _≤_ at earlier peer projected
  simp only [received,DescentSixParty.Chronology.NativePhase.seq,names_seq,receivedBill,scalarNames]
  dsimp only [donorPhase,DescentContactDonorFront.Shape.native,contactPhase,scalarPhase,phase,scalar] at *
  omega

end
end Hierarchy.DescentDatedAddressBook.CandidateFront

end OAI

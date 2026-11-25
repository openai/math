import OAI.Hierarchy.DescentResetMixedReadPitch
import OAI.Hierarchy.DescentOriginalMarkerTail
import OAI.Hierarchy.DescentResetSenderFieldWidth
import OAI.Hierarchy.DescentPhysicalResetSceneRead

namespace OAI
/-! # Operand and address bounds for the original packet on the reached reset date -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentResetNewActorDirectory DescentDatedAddressBook DescentCompiler DescentColonies DescentDenseHostOrder DescentResetLocalRoster
open DescentPackedPrivateMenu DescentResetPeerUnionRAM DescentPackedColony DescentSIMDLookup
open DescentGroupPeerOrder DescentSortedRoster DescentContactOutputShape DescentPacking.PackedMatch.Local.Stage
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
set_option quotPrecheck false
set_option hygiene false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "A" => input.placement
local notation "H" => S.hostSize i
local notation "J" => 2^(T).commonDepth
local notation "r" => (Z).k-(T).commonDepth
local notation "ht" => GroupStage.depthBound D n f g
local notation "shelf" => (DescentDenseHostOrder.roster (Z).graph r ht).card
local notation "gs" => S.groupCount (i+1)
local notation "cap₀" => max (Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge) (2^(ht+1))
local notation "oldWidth" => DescentPackedPrivateMenu.fieldBits (Z).graph r ht (2^r*(2*(A).cap))
    (DescentRecordedRotorLayers.width f (A).cap) C (Z).width
variable (oldBatch batch : ℕ) (calendar : List ℕ) (paid : (A).cap=(calendar.take i).prod*256)
local notation "cap" => (calendar.take i).prod*256
local notation "field₀" => ResetMiddle.fieldWidth D cap n k ht
local notation "table₀" => CandidateSheets.fromBoard S ctl.board k tail i D f g cap batch
local notation "meta₀" => (table₀).metaBits
local notation "month" => CandidateFront.menu S ctl.board k tail i D f g oldBatch batch C ctl.bitsR calendar
local notation "good" => contactOutputs B H oldBatch field₀ (Nat.clog 2 (D+2)) (Nat.clog 2 (D+3)) gs (2^k)
    batch (month).contact.outputBits meta₀
local notation "deck" => privateProjection («H»:=H) (field:=oldWidth) B oldBatch batch meta₀
variable {date : PhysicalReset} {floor bw : ℕ} (I : date.DateInputs floor bw)
local notation "v₀" => date.successor
local notation "base₀" => date.rebased floor
local notation "phys₀" => (v₀).front
local notation "peer₀" => (phys₀).peer
local notation "pitch₀" => (phys₀).contactLayout ((v₀).actorEnd base₀)
local notation "Q₀" => (v₀).privateShape
local notation "K₀" => (v₀).contactShape
local notation "don₀" => (phys₀).donorStart ((v₀).actorEnd base₀)
local notation "used" => Fintype.card B.next.V
local notation "rawSize" => H*shelf
local notation "L" => 2^(S.groupWidth k tail i+k-(T).commonDepth)
local notation "K" => 2*(A).cap
local notation "F₀" => DescentOldContactSender.count (A).degree L (A).cap (Z).n r

open DescentResetPeerUnionRAM
local notation "entry" => (v₀).actorEnd base₀
local notation "markerBits" => (month).peer.bits
local notation "geometry" => peerLayout B ((month).oldKeys entry) H oldBatch (month).privateBits ((month).stemField+2) markerBits
local notation "donorAt" => (geometry).endAddress
local notation "contactAt" => (good).donor.endAddress donorAt
local notation "measured" => contactLayout B contactAt H oldBatch field₀ markerBits
local notation "stop₀" => (v₀).trunkEnd base₀

structure PacketRankEarly : Prop where
  endRoom : (measured).endAddress < 2^bw
  packedMarker : oldBatch*max (field₀*8) markerBits ≤ bw/2
  wordPositive : 0 < field₀
  packedDonor : ((good).donor.sender donorAt).Packed bw
  boardWidth : oldBatch*max (field₀*(measured).oldFields) (measured).viewBits ≤ bw/2
  shapeWidth : shelf ≤ 2^field₀
  markerWidth : ((A).degree+1)*shelf < 2^markerBits
  room : Program.endAddress (measured).endAddress H shelf (A).degree (peerEvidenceRows B) markerBits oldBatch < 2^bw
  right : (measured).endAddress ≤ stop₀
  remote : (good).marker stop₀ + H*chunks J oldBatch < 2^bw
  items : oldBatch*max (field₀*(L*(2*(A).cap)+1)) field₀ ≤ bw/2
  dateEnd : (good).endAddress stop₀ < 2^bw
  joints : shelf*2^Nat.clog 2 ((A).degree+2) ≤ 2^meta₀

include paid in
/-- The original predecessor directory, contact census, and signed sender rows
all fit the word and address spaces selected for the same registered reset. -/
theorem named_packet_rank_early (front : (v₀).front=month)
    (ss : (v₀).sheets=table₀) (wideBoard : h ≤ 2^k)
    (cal : MixedGeometry B oldBatch batch calendar v₀ base₀)
    (ok : I.Ready) (aligned : ResetOutput.ContactAligned v₀)
    {payload : ℕ} (tables : ∀t,t∈(v₀).rootUnits ∨ t∈(v₀).receiverUnits →
      t*(v₀).receiver.lanes ≤ payload/2) (wide : payload ≤ bw) :
    PacketRankEarly (bw:=bw) B oldBatch batch calendar (date:=date) (floor:=floor) := by
  have donor : (month).donor = (good).donor := canonical_donor B oldBatch batch field₀ meta₀ calendar paid
  have hsrc : (month).donorStart entry=donorAt :=
    canonical_raw_end B oldBatch batch field₀ meta₀ calendar entry
  have stop : (month).donorEnd entry=contactAt := by
    change (month).donor.endAddress ((month).donorStart entry)=_
    rw [hsrc,donor]
  have chart : (phys₀).contactLayout entry=measured := by
    rw [front]
    exact (canonical_contact B oldBatch batch field₀ meta₀ calendar paid entry).trans
      (congrArg (fun z=>contactLayout B z H oldBatch field₀ markerBits) stop)
  have actual : (phys₀).peers entry=(measured).endAddress :=
    congrArg DescentContactPreROM.Layout.endAddress chart
  have evidence : (peer₀).evidence=peerEvidenceRows B := by
    rw [front]
    exact (canonical_probes B oldBatch batch field₀ meta₀ calendar paid).1
  have extent : (peer₀).three ((phys₀).peers entry) =
      Program.endAddress (measured).endAddress H shelf (A).degree (peerEvidenceRows B) markerBits oldBatch := by
    unfold PeerAperture.three
    rw [actual,cal.oldCount,cal.peerShapes,cal.oldDegree,evidence,front]
    rfl
  have upper : (peer₀).three ((phys₀).peers entry) ≤ (peer₀).endAddress ((phys₀).peers entry) := by
    unfold PeerAperture.endAddress PeerAperture.threshold PeerAperture.self
    rw [DescentResetSelfPortsRAM.extent]
    exact ((Nat.le_add_right ..).trans (Nat.le_add_right ..)).trans (Nat.le_add_right ..)
  have trunk : (peer₀).three ((phys₀).peers entry) ≤ stop₀ := by
    have parent : (peer₀).endAddress ((phys₀).peers entry) ≤ (phys₀).parentStart entry := Nat.le_add_right ..
    have room := (phys₀).front_order entry
    have out : (phys₀).mixed entry ≤ (phys₀).trunkEnd entry :=
      (DescentResetTrunkCompactProgram.grow ..).trans (Nat.le_add_right ..)
    change _ ≤ (phys₀).trunkEnd entry
    omega
  have first : (measured).endAddress ≤ (peer₀).three ((phys₀).peers entry) := by
    rw [←actual,(peer₀).three_extent]
    exact Nat.le_add_right ..
  have limits := original_read_pitch B oldBatch batch calendar paid I front aligned tables wide donorAt
  have sender := original_sender_pitch B oldBatch batch calendar paid front aligned tables wide donorAt
  have tagWidth := CandidateFront.setup_marker_fits S ctl.board k tail i D f g oldBatch batch field₀ meta₀ C ctl.bitsR calendar
  have keyWidth := cal.fieldWidth
  rw [ss] at keyWidth
  refine ⟨(first.trans trunk).trans_lt ok.trunk,sender.1,?_,sender.2,limits.2.2.1,?_,?_,
    extent ▸ trunk.trans_lt ok.trunk,first.trans trunk,original_marker_tail B oldBatch batch calendar I cal ok,
    limits.2.2.2,?_,?_⟩
  · have hpos := aligned.inputField
    rw [front] at hpos
    exact hpos
  · rw [B.public_hub_slots]
    exact ResetMiddle.sender_shapes D cap n k ht ctl.board wideBoard
  · rw [input.branch,B.public_hub_slots]
    exact tagWidth
  · rw [←cal.contactDeck]
    exact ok.mass
  · rw [input.branch,keyWidth]
    have room := Nat.le_pow_clog (by decide : 1 < 2) (shelf+1)
    calc
      _ ≤ 2^Nat.clog 2 (shelf+1) * 2^Nat.clog 2 (D+2) :=
        Nat.mul_le_mul_right _ ((Nat.le_succ _).trans room)
      _ = 2^(Nat.clog 2 (D+2)+Nat.clog 2 (shelf+1)) := by rw [pow_add,Nat.mul_comm]
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (Nat.le_max_right ..)

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI

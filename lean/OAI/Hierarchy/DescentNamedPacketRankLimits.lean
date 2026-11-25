import OAI.Hierarchy.DescentResetMixedReadPitch
import OAI.Hierarchy.DescentNamedResetSheets
import OAI.Hierarchy.DescentNamedPacketRankEarly

namespace OAI
/-! # The rank solver reads the funded reset field and capacity at the selected lane pitch -/
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


/-- The sizes of the actually executed late rank and mask lookups and the
alphabet of the recorded reset window cells at that same date. -/
structure PacketRankLimits : Prop where
  trunkRoom : (month).trunkEnd ((v₀).actorEnd base₀)<2^bw
  width : (meta₀*7)*batch≤bw
  degreeWord : B.next.placement.degree+1<2^meta₀
  capWord : B.next.placement.cap<2^meta₀
  alphabet : 5≤2^meta₀
  wordAlphabet : 5≤2^bw
  lanePositive : 0<I.masked.lanes
  rankFit : I.masked.lanes*max (I.masked.field*5) I.masked.field≤bw/2
  maskFit : I.masked.lanes*max (I.masked.field*9) (I.masked.field*7)≤bw/2

include paid in
theorem named_packet_rank_limits (front : (v₀).front=month)
    (sheets : (v₀).sheets=table₀) (ok : I.Ready) (positive : 0<batch)
    (aligned : ResetOutput.ContactAligned v₀)
    {payload : ℕ} (tables : ∀t,t∈(v₀).rootUnits ∨ t∈(v₀).receiverUnits →
      t*(v₀).receiver.lanes≤payload/2) (wide : payload≤bw) :
    PacketRankLimits B oldBatch batch calendar I:=by
  have lr : I.masked.lanes=batch:=congrArg CandidateSheets.lanes sheets
  have fld : I.masked.field=meta₀:=congrArg CandidateSheets.metaBits sheets
  have pitches:=(v₀).mixed_read_pitch aligned tables wide
  have rankFit : I.masked.lanes*max (I.masked.field*5) I.masked.field≤bw/2:=pitches.1
  have maskFit : I.masked.lanes*max (I.masked.field*9) (I.masked.field*7)≤bw/2:=pitches.2.1
  have win : max 5 (2^g*cap+2)≤2^meta₀:=by
    apply (Nat.le_pow_clog (by decide : (1:ℕ)<2) (max 5 (2^g*cap+2))).trans
    apply Nat.pow_le_pow_right (by decide)
    exact le_max_left ..
  have alpha : 5≤2^meta₀:=(le_max_left 5 _).trans win
  have capOK : B.next.placement.cap<2^meta₀:=by
    rw [B.next_capacity,paid]
    exact (by omega : 2^g*cap< max 5 (2^g*cap+2)).trans_le win
  have fit : (meta₀*7)*batch≤bw:=by
    rw [←fld,Nat.mul_comm _ batch,←lr]
    exact (Nat.mul_le_mul_left _ (le_max_right ..)).trans (maskFit.trans (Nat.div_le_self ..))
  have bitsOK : meta₀≤bw:=((Nat.le_mul_of_pos_right meta₀ (by decide : 0<7)).trans
    (Nat.le_mul_of_pos_right (meta₀*7) positive)).trans fit
  have degreeOK : B.next.placement.degree+1<2^meta₀:=by rw [B.next.branch];omega
  exact ⟨by simpa only [ResetOutput.trunkEnd,front] using ok.trunk,fit,degreeOK,capOK,alpha,
    alpha.trans (Nat.pow_le_pow_right (by decide) bitsOK),lr.symm ▸ positive,rankFit,maskFit⟩


include paid in
theorem named_packet_rank_rooms (front : (v₀).front=month) (sheets : (v₀).sheets=table₀)
    (wideBoard : h≤2^k) (cal : MixedGeometry B oldBatch batch calendar v₀ base₀) (ok : I.Ready)
    (positive : 0<batch) (aligned : ResetOutput.ContactAligned v₀)
    {payload : ℕ} (tables : ∀t,t∈(v₀).rootUnits ∨ t∈(v₀).receiverUnits →
      t*(v₀).receiver.lanes≤payload/2) (wide : payload≤bw) :
    PacketRankEarly (bw:=bw) B oldBatch batch calendar (date:=date) (floor:=floor) ∧
    PacketRankLimits B oldBatch batch calendar I:=
  ⟨named_packet_rank_early B oldBatch batch calendar paid I front sheets wideBoard cal ok aligned tables wide,
    named_packet_rank_limits B oldBatch batch calendar paid I front sheets ok positive aligned tables wide⟩

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI

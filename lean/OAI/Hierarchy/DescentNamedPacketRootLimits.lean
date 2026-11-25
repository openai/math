import OAI.Hierarchy.DescentNamedCensusPacketLimits
import OAI.Hierarchy.DescentNamedResetOutput
import OAI.Hierarchy.DescentDatedOperandHeader
import OAI.Hierarchy.DescentResetReceiverPitch
import OAI.Hierarchy.DescentRecipeClosedReset
import OAI.Hierarchy.DescentPacketSenderLimits
import OAI.Hierarchy.DescentCapCalendarPositive

namespace OAI
/-! # Source-word and address limits at the reached predecessor reset -/
noncomputable section
set_option quotPrecheck false
set_option hygiene false
namespace Hierarchy.DescentDatedAddressBook
open DescentSixParty DescentCompiler DescentDenseHostOrder DescentResetLocalRoster

theorem ResetOutput.root_field_width (v : ResetOutput) : v.middle.rootField≤v.groupWidth :=by
  let middle:=v.middle
  let arity:=DescentFallbackPeriod.Projected.Receiver.arityLimit middle.rootDegree (2^middle.rootDepth)
    v.front.donor.cap middle.rotorBits middle.rootDepth
  have member : middle.rootField*(arity+1)∈v.rootUnits:=by simp [ResetOutput.rootUnits,arity,middle]
  exact (Nat.le_mul_of_pos_right _ (Nat.succ_pos _)).trans (v.groupWidth_fit (.inl member))

namespace PhysicalReset
variable {F X : Type} [Field F] {d : ℕ} {bits : X→ℕ} {W : MarkedWorld F d X bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z wire hist D n h C f g cut tail : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "Z" => B.reset
local notation "A" => input.placement
local notation "r" => (Z).k-B.terminals.commonDepth
local notation "amp" => (A).wire*((A).z*G.b)*(A).cap
local notation "ht" => GroupStage.depthBound D n f g

structure PacketRootLimits (nbits t field w : ℕ) : Prop where
  level : r<2^nbits
  one : 1<2^nbits
  mass : 2^r*amp<2^nbits
  codes : 2*DescentFallbackShapeTable.rows r (2^(Z).n)≤2^t
  active : 0<amp
  quotaPos : 0<quota S.rounds
  degreePos : 0<32*Nat.clog 2 (2*(A).degree)
  precision : t≤field
  depthFit : r+1<2^field
  capFit : (A).cap<2^field
  baseRoom : max (max r (2^(Z).n)) (2^r)<2^field
  dimension : (Z).n<field
  socketRoom : rootSlots r (2^(Z).n)*(2^(Z).n+2^ht)<2^field
  heightRoom : ht<2^field
  portRoom : (A).degree≤2^field
  low : ht+2<w
  rankRoom : ht+2≤field

variable (p drift degree payload e previous M nextM oldLanes primitiveLanes printedBits : ℕ)
  (venue : StageVenueTail.Date) (io : DescentPacking.PackedMatch.Local.Stage.Dated.Operands) (floor w : ℕ)
local notation "v" => (named G S ctl.board k tail i p f g drift degree payload e previous M nextM C ctl.bitsR
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor).successor
local notation "cc" => S.groupWidth k tail i
local notation "cal" => capCalendar G.b S.rounds g S.height
local notation "cap" => ((cal).take i).prod*256

theorem named_packet_root_limits (recorded : B.Recorded p)
    (gr : z=S.grainAt G.b p (i+1)) (fee : wire=S.epochPower^S.priceExponent) (branch : G.b≤2^S.capGain)
    (degreeAt : venue.degree=D) (capAt : (A).cap=cap) (positiveD : 0<32*Nat.clog 2 (2*venue.degree))
    (small : 8*(v).groupWidth≤payload) (word : payload≤w) :
    PacketRootLimits B (k+S.localWalshBits p (cc+k) f (quota S.rounds)+2) (2*k+n+2) (v).middle.rootField w:=by
  obtain ⟨lev,one,mass,codes⟩:=ClosedReset.Window.named_census_packet_limits B p gr fee branch
  have radius : r=k:=by rw [B.keyWidth,B.commonDepth,Nat.add_sub_cancel_left]
  have widths:=ResetMiddle.packet_sender_limits D cap n k ht
  have field : (v).middle.rootField=ResetMiddle.fieldWidth D cap n k ht:=by
    change ResetMiddle.fieldWidth venue.degree cap n k (GroupStage.depthBound venue.degree n f g)=_
    rw [degreeAt]
  have widthWord := (v).root_field_width
  rw [field] at widthWord
  have liveMass : 0<amp:=by
    rw [input.edges,input.grain,capAt,gr,fee]
    exact Nat.mul_pos (Nat.mul_pos (Nat.pow_pos (Nat.two_pow_pos _))
      (Nat.mul_pos (S.grain_positive G.base_pos recorded.positive _) G.base_pos))
      (Nat.mul_pos (Chronology.DonorDate.prefix_cap_pos G.b S.rounds g S.height i G.base_pos) (by decide))
  have degreePos : 0<32*Nat.clog 2 (2*(A).degree):=by simpa only [input.branch,degreeAt] using positiveD
  constructor
  · simpa only [radius] using lev
  · exact one
  · simpa only [radius] using mass
  · simpa only [radius,B.dimension] using codes
  · exact liveMass
  · exact Nat.succ_pos _
  · exact degreePos
  · simpa only [field] using widths.precision
  · simpa only [field,radius] using widths.depthFit
  · simpa only [field,capAt] using widths.capFit
  · simpa only [field,B.dimension,radius] using widths.baseRoom
  · simpa only [field,B.dimension] using widths.dimension
  · simpa only [field,B.dimension,radius] using widths.socketRoom
  · simpa only [field] using widths.heightRoom
  · simpa only [field,input.branch] using widths.portRoom
  · have strict:=widths.rankStrict
    omega
  · simpa only [field] using widths.rankRoom

end PhysicalReset
end Hierarchy.DescentDatedAddressBook
end

end OAI

import OAI.Hierarchy.DescentNamedOperandWordRoom
import OAI.Hierarchy.DescentRetainedOperandCounts
import OAI.Hierarchy.DescentResetRankCalendar
import OAI.Hierarchy.DescentOccurrenceAllowance

namespace OAI
/-! Word room for the retained operand, its native donor and both argument rectangles at a reset. -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentDatedAddressBook DescentOperandWidth
noncomputable section
set_option quotPrecheck false

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : DescentCompiler.AtomSchedule}
  {k age grain oldDegree wire hist n h C f g cut tail : ℕ}
  {incoming : Reached W G q ε S k age grain oldDegree wire hist}
  {ctl : ResetRates G S k oldDegree n h C f g cut tail} (B : ClosedReset incoming ctl)
  (p drift degree payload e previous M nextM packet : ℕ) (old : ResetOutput.Prior) (start w : ℕ)
local notation "v" => ResetOutput.fromBoard G S ctl.board k tail age p f g drift degree payload e previous M nextM
  C packet old start
local notation "chart" => (v).setup
local notation "r" => (chart).retained

theorem named_retained_codec_room
    (degreeAt : old.venue.degree=incoming.placement.degree)
    (capAt : incoming.placement.cap=((capCalendar G.b S.rounds g S.height).take age).prod*256) :
    DescentSignedCableCodec.width incoming.placement.degree incoming.placement.cap≤(chart).fieldBits:=by
  rw [←degreeAt,capAt]
  exact (Nat.le_max_left ..).trans ((Nat.le_max_right ..).trans (Nat.le_max_right ..))

theorem named_retained_operand_bounds (height : 0<S.height) (base : G.b≤2^S.capGain)
    (capAt : incoming.placement.cap=((capCalendar G.b S.rounds g S.height).take age).prod*256)
    (previousNodes : old.nodes≤S.retainedNodes) (previousArgs : old.arguments≤S.retainedArgumentsAt G drift)
    (room : (v).finalEnd start<2^w) :
    (r).bits*(chart).lanes≤w ∧ (r).bits≤(v).receiver.valueBits ∧ (r).donors<2^(r).bits ∧
    (chart).cable.units*B.next.placement.cap≤2^(chart).cable.fieldBits ∧
    max (B.next.placement.degree+1) (B.next.placement.cap+1)≤2^(v).receiver.signedBits ∧
    (r).nodes*(r).args≤2^(r).bits ∧ (r).previousNodes*(r).previousArgs≤2^(r).bits:=by
  have small:=ResetOutput.named_ticket_limits G S ctl.board k tail age p f g drift degree payload e previous M
    nextM C packet old start
  have nonempty : 0<2*(v).receiver.candidates:=
    (Nat.zero_lt_succ _).trans_le (by simpa only [Nat.add_comm 1] using small.2.1)
  have packed:=(v).physical_operand_rooms start w nonempty (Nat.le_max_left ..) room
  have donated : (r).donors=2^k:=
    (S.previousGeometry G k tail drift degree p age payload old.nodes old.arguments old.operandLanes
      ctl.base ctl.radix B.age).2.2.2.2.2.1
  have donorsFit : (r).donors<2^(r).bits:=by
    rw [donated]
    exact donor_count_lt G S k tail drift degree p B.age
  have actualCap:=S.local_capacity height B.age B.next.valid.capacity
  have quantity : ResetInput.calendarLanes S G.b (age+1)≤S.epochPower^S.localGrainExponent:=
    (S.grain_le_first G.b 1 (age+1) G.base_pos).trans (by simpa only [Nat.one_mul] using S.first_width_payload height base 1)
  have chunks : ResetInput.calendarLanes S G.b (age+1)*B.next.placement.cap≤ slices S:=by
    simpa only [slices,pow_add] using Nat.mul_le_mul quantity actualCap
  have digitRoom:=signed_digit_room B
  rw [capAt] at digitRoom
  have valueRoom : max (B.next.placement.degree+1) (B.next.placement.cap+1)≤2^(v).receiver.signedBits:=
    digitRoom.le.trans (Nat.pow_le_pow_right (by decide) (Nat.le_max_left ..))
  have array : S.retainedNodes*S.retainedArgumentsAt G drift≤2^(r).bits:=
    (retained_rectangle_lt G S k tail drift degree p).le
  exact ⟨packed.2.1,le_rfl,donorsFit,
    (rangeField G S chunks).le.trans (Nat.pow_le_pow_right (by decide) small.2.2),valueRoom,array,
    (Nat.mul_le_mul previousNodes previousArgs).trans array⟩
end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI

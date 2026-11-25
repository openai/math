import OAI.Hierarchy.DescentClosedReset
import OAI.Hierarchy.DescentResetSerialRoom

namespace OAI
/-! The real dated word width covers both original old-socket ordinals and signed serials. -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentHostDegree DescentOperandWidth
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
    {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
    (B : ClosedReset input ctl)

include B in
theorem serial_roster_space (rest drift degree p : ℕ) :
    2*max (publicCap S) (2^k*(2*input.placement.cap))<2^(recordBits G S k rest drift degree p):=by
  have prefixBits : S.capGain*i≤(S.hostGain+S.capGain)*((S.rounds+1)*S.height):=
    Nat.mul_le_mul (Nat.le_add_left ..) B.age.le
  have step : 8+S.capGain*i+3≤k:=by
    have seed:=ctl.seed
    unfold packExponent at seed
    rw [ctl.fixed]
    unfold groupBits
    omega
  exact roster_room G S k rest drift degree p input.placement.cap i B.age input.valid.capacity step

theorem serial_dated_space (rest drift degree p : ℕ) :
    2*max B.next.placement.cap (2^k*(2*input.placement.cap))<2^(recordBits G S k rest drift degree p):=by
  have volume:B.next.placement.cap≤publicCap S :=
    B.next.valid.capacity.trans (Nat.pow_le_pow_right (by decide)
      (Nat.add_le_add_left (Nat.mul_le_mul_left _ B.age) _))
  exact (Nat.mul_le_mul_left _ (max_le_max_right _ volume)).trans_lt (serial_roster_space B rest drift degree p)
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI

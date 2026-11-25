import OAI.Hierarchy.DescentOperandWidth

namespace OAI
/-! The reset operand field accommodates both the signed serial and the old socket number. -/
namespace Hierarchy.DescentOperandWidth
open DescentCompiler DescentSixParty

theorem roster_room {F : Type} [Field F] (G : PoweredGadget F) (S : AtomSchedule)
    (k tail drift degree p cap age : ℕ) (at_ : age < S.length)
    (paid : cap ≤ 2^(8+S.capGain*age)) (step : 8+S.capGain*age+3 ≤ k) :
    2*max (publicCap S) (2^k*(2*cap)) < 2^(recordBits G S k tail drift degree p) := by
  have publicRoom : 2*publicCap S < 2^(s G S k tail drift degree) := by
    have boundRaw : 2*publicCap S ≤ raw S := by unfold raw; omega
    apply numeric G S
    exact boundRaw.trans ((Nat.le_max_left ..).trans ((Nat.le_max_right ..).trans (Nat.le_max_right ..)))
  have earlier : k ≤ k*S.length := Nat.le_mul_of_pos_right _ (Nat.zero_le age |>.trans_lt at_)
  have stampRoom : k+(8+S.capGain*age)+2 < S.stampBits k tail := by
    change _ < tail+k*(S.length-0)+k
    rw [Nat.sub_zero]
    omega
  have oldRoom : 2*(2^k*(2*cap)) < 2^(s G S k tail drift degree) := calc
    _ ≤ 2*(2^k*(2*2^(8+S.capGain*age))) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ paid))
    _ = 2^(k+(8+S.capGain*age)+2) := by simp only [pow_add]; ring
    _ < 2^(S.stampBits k tail) := Nat.pow_lt_pow_right (by decide) stampRoom
    _ ≤ _ := Nat.pow_le_pow_right (by decide) ((Nat.le_max_left ..).trans (Nat.le_max_right ..))
  apply Nat.lt_of_lt_of_le _ (Nat.pow_le_pow_right (by decide)
    (Nat.le_max_left (s G S k tail drift degree) (Nat.log 2 p+1)))
  rcases le_total (publicCap S) (2^k*(2*cap)) with smaller | larger
  · simpa only [max_eq_right smaller] using oldRoom
  · simpa only [max_eq_left larger] using publicRoom

end Hierarchy.DescentOperandWidth

end OAI

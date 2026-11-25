import OAI.Hierarchy.DescentOperandWidth
import OAI.Hierarchy.DescentCalendarNumbers

namespace OAI
/-! # Identical recorded operand widths in the registered venue and terminal decoder -/
namespace Hierarchy.DescentOperandWidth
open DescentCompiler DescentCompiler.TerminalScale DescentSixParty Filter
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F)

theorem recordBits_eq_cubic (S:AtomSchedule) (k tail drift degree p:ℕ) (covered:degree≤ raw S) :
    recordBits G S k tail drift degree p=recordBits G S k tail drift 3 p:=by
  have cubic:3≤ raw S:=by unfold raw;omega
  simp only [recordBits,s,bound,max_eq_left covered,max_eq_left cubic]

theorem eventually_cubic_records (t f g reset B degreeMax : ℕ) (positive:0< B) :
    ∀ᶠ h:ℕ in atTop,∀M tail k drift degree p,degree≤ degreeMax→
      let S:=stageNumbers G t (Nat.log 2 h/(2*B)) f g reset M tail
      recordBits G S k tail drift degree p=recordBits G S k tail drift 3 p:=by
  filter_upwards [eventually_ge_atTop (2^(degreeMax*(2*B)))] with h late
  intro M tail k drift degree p bound_
  let J:=Nat.log 2 h/(2*B)
  let S:=stageNumbers G t J f g reset M tail
  have enough:degreeMax≤ J:=
    (Nat.le_div_iff_mul_le (by omega : 0<2*B)).2 (Nat.le_log_of_pow_le (by decide) late)
  have length:J≤ S.length:=by
    change J≤(t+1)*J
    exact Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  have cap:0< S.capGain:=by change 0<capRate G t g;unfold capRate;omega
  have exponent:degree≤8+S.capGain*S.length:=by
    have mass:S.length≤S.capGain*S.length:=Nat.le_mul_of_pos_left _ cap
    omega
  have words:degree≤ publicCap S:=exponent.trans Nat.lt_two_pow_self.le
  apply recordBits_eq_cubic G S k tail drift degree p
  unfold raw
  omega

end
end Hierarchy.DescentOperandWidth

end OAI

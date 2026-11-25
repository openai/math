import OAI.Hierarchy.DescentGrainCalendar
import OAI.Hierarchy.DescentRetainedArgumentLimit

namespace OAI
/-! # The original three input blocks fit the retained argument capacity -/
namespace Hierarchy.DescentSixParty.AtomSchedule
open DescentCompiler
noncomputable section
variable {F : Type} [Field F] (S : DescentCompiler.AtomSchedule) (G : PoweredGadget F)

theorem seed_argument_capacity (p drift : ℕ) (late : 0<S.height) (base : G.b≤2^S.capGain) :
    3*(S.firstWidth G.b p/p)≤S.retainedArgumentsAt G drift :=by
  by_cases z:p=0
  · simp [z]
  have positive : 0<p:=Nat.pos_of_ne_zero z
  have bits : 3*(S.firstWidth G.b p/p)≤2^(2+S.capGain*(S.rounds*S.height+1)) :=by
    rw [DescentCompiler.AtomSchedule.firstWidth,S.grain_initial,Nat.mul_assoc,Nat.mul_div_cancel_left _ positive]
    rw [←pow_succ]
    calc 3*G.b^(S.rounds*S.height+1)≤(2^2)*(2^S.capGain)^(S.rounds*S.height+1) :=
        Nat.mul_le_mul (by decide) (Nat.pow_le_pow_left base _)
      _ = _ :=by rw [←pow_mul,←pow_add]
  have exp : 2+S.capGain*(S.rounds*S.height+1)≤S.height*(operandExponent G S) :=by
    unfold operandExponent DescentCompiler.AtomSchedule.localGrainExponent
    have a:=Nat.mul_le_mul_left S.capGain late
    nlinarith only [a,late,Nat.zero_le (S.height*G.C),Nat.zero_le (S.height*G.k),
      Nat.zero_le (S.height*G.b),Nat.zero_le (S.height*S.capGain)]
  apply bits.trans
  calc 2^(2+S.capGain*(S.rounds*S.height+1))≤2^(S.height*(operandExponent G S)) :=
      Nat.pow_le_pow_right (by decide) exp
    _ = S.retainedArguments G := by rw [pow_mul];rfl
    _ ≤ S.retainedArgumentsAt G drift := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)

end
end Hierarchy.DescentSixParty.AtomSchedule


namespace Hierarchy.DescentCompiler.AtomSchedule
export Hierarchy.DescentSixParty.AtomSchedule (seed_argument_capacity)
end Hierarchy.DescentCompiler.AtomSchedule

end OAI

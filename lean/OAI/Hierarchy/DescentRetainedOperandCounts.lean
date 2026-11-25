import OAI.Hierarchy.DescentOperandWidth

namespace OAI
/-! The actual donor table and the retained argument rectangle fit one operand field. -/
namespace Hierarchy.DescentOperandWidth
open DescentCompiler DescentSixParty
variable {F : Type} [Field F] (G : PoweredGadget F) (S : DescentCompiler.AtomSchedule)
  (k tail drift degree p : ℕ)

theorem donor_count_lt {age : ℕ} (active : age<S.length) :
    2^k<2^(recordBits G S k tail drift degree p):=by
  have exponent : k<s G S k tail drift degree:=by
    by_cases zero : k=0
    · rw [zero]
      exact (by decide : 0<2).trans_le (wide G S 0 tail drift degree)
    · have positive:=Nat.mul_pos (Nat.pos_of_ne_zero zero) (Nat.zero_lt_of_lt active)
      have stamp : k<S.stampBits k tail:=by
        unfold DescentCompiler.AtomSchedule.stampBits DescentCompiler.AtomSchedule.groupWidth
        simp only [Nat.sub_zero]
        omega
      exact stamp.trans_le ((Nat.le_max_left ..).trans (Nat.le_max_right ..))
  exact Nat.pow_lt_pow_right (by decide) (exponent.trans_le (Nat.le_max_left ..))

theorem retained_rectangle_lt :
    S.epochPower^S.localTokenExponent*((drift+1)*S.epochPower^(operandExponent G S)) <
      2^(recordBits G S k tail drift degree p):=by
  have count : S.epochPower^S.localTokenExponent*((drift+1)*S.epochPower^(operandExponent G S)) =
      NativeBranch.privateSlotCapacity G S drift:=by
    unfold NativeBranch.privateSlotCapacity
    rw [pow_add]
    ac_rfl
  rw [count]
  have fits : NativeBranch.privateSlotCapacity G S drift≤bound G S drift degree:=
    (Nat.le_max_left ..).trans (Nat.le_max_left ..)
  exact (numeric G S (k:=k) (tail:=tail) fits).trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_max_left ..))

end Hierarchy.DescentOperandWidth

end OAI

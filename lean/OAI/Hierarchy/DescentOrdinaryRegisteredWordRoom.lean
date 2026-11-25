import OAI.Hierarchy.DescentOperandWidth
import OAI.Hierarchy.DescentRetainedArgumentLimit

namespace OAI
/-! The actual flattened per-node argument count fits the uniform dated operand word. -/
namespace Hierarchy.DescentOperandWidth
open DescentSixParty DescentCompiler
variable {F:Type} [Field F] (G:PoweredGadget F) (S:AtomSchedule)

theorem registered_arguments (k tail drift degree p:ℕ) :
    S.retainedArgumentsAt G drift < 2^(recordBits G S k tail drift degree p) := by
  have wide:S.retainedArgumentsAt G drift≤NativeBranch.privateSlotCapacity G S drift:=by
    apply Nat.mul_le_mul_left
    exact Nat.pow_le_pow_right (show 0<S.epochPower from Nat.two_pow_pos _) (Nat.le_add_right ..)
  have field:=numeric (k:=k) (tail:=tail) (degree:=degree) G S
    (wide.trans ((Nat.le_max_left ..).trans (Nat.le_max_left ..)))
  exact field.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_max_left ..))

end Hierarchy.DescentOperandWidth

end OAI

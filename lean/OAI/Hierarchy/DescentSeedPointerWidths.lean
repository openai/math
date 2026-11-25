import OAI.Hierarchy.DescentOperandWidth
import OAI.Hierarchy.DescentSeedChosenLayoutCore
import OAI.Hierarchy.DescentSeedInitialArgumentCapacity

namespace OAI
/-! # All four original pointer components fit in the calibrated seed operand header -/
namespace Hierarchy.DescentDatedSeedStartup
open DescentSixParty DescentCompiler
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F) (S : AtomSchedule)

theorem selected_pointer_widths (h k tail gain p drift degree f quota base field wire history : ℕ)
    (groups : S.baseGroups=2^tail) (radix : S.radix=2^k) (epoch : 0<S.height) (budget : G.b≤2^S.capGain) :
    let l:=selectedLayout G S h k tail gain p drift degree f quota base field wire history
    3<2^l.operandBits ∧ S.copies≤2^l.operandBits ∧ l.groupsPerNode≤2^l.operandBits :=by
  let size:=DescentOperandWidth.s G S k tail drift degree
  let b:=DescentOperandWidth.recordBits G S k tail drift degree p
  have widen : 2^size≤2^b:=Nat.pow_le_pow_right (by decide) (Nat.le_max_left ..)
  change 3<2^b ∧ S.copies≤2^b ∧ S.firstWidth G.b p/p≤2^b
  refine ⟨(show 3<2^2 by decide).trans_le ((Nat.pow_le_pow_right (by decide)
    (DescentOperandWidth.wide G S k tail drift degree)).trans widen),?_,?_⟩
  · by_contra! insufficient
    have fits:=DescentOperandWidth.original G S (k:=k) (tail:=tail) (drift:=drift) (degree:=degree)
      groups radix (⟨2^b,insufficient⟩:Fin S.copies)
    exact (Nat.not_lt_of_ge widen) fits
  · have project:=S.seed_argument_capacity G p drift epoch budget
    have earlier : S.firstWidth G.b p/p≤S.retainedArgumentsAt G drift:=by omega
    have one : 1≤S.epochPower:=Nat.two_pow_pos _
    have privateRoom : S.retainedArgumentsAt G drift≤NativeBranch.privateSlotCapacity G S drift:=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right one (Nat.le_add_right _ _))
    have legal : S.firstWidth G.b p/p≤DescentOperandWidth.bound G S drift degree:=
      ((earlier.trans privateRoom).trans (Nat.le_max_left ..)).trans (Nat.le_max_left ..)
    exact ((DescentOperandWidth.numeric G S (k:=k) (tail:=tail) legal).le).trans widen

end
end Hierarchy.DescentDatedSeedStartup

end OAI

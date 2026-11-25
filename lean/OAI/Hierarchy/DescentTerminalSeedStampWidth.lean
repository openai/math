import OAI.Hierarchy.DescentResetDigits
import OAI.Hierarchy.DescentCalendarNumbers

namespace OAI
/-! # Width of the immutable exterior copy identifier in a packed scalar record -/
namespace Hierarchy.DescentCompiler.AtomSchedule

def stampBits (S:AtomSchedule) (k tail:ℕ) := S.groupWidth k tail 0+k

theorem stamp_room (S:AtomSchedule) {k tail:ℕ} (base:S.baseGroups=2^tail) (radix:S.radix=2^k)
    (j:Fin S.copies) : j.val<2^(S.stampBits k tail) := by
  have bound:=j.isLt
  simpa only [stampBits,groupWidth,Nat.sub_zero,copies,base,radix,pow_add,pow_mul,
    Nat.pow_succ,pow_zero,one_mul,Nat.mul_assoc] using bound

/-- The entire copy identifier, including digits later mixed by the reset matrix, takes
quadratically many epoch-index bits. The bound is uniform in input size and copy rank. -/
theorem stamp_width (S:AtomSchedule) (J t k τ κ:ℕ) (dates:S.length=(t+1)*J)
    (active:k≤κ*(J+1)) :
    S.stampBits k (τ*(J+1))≤(τ+κ*(t+2))*(J+1)^2 := by
  change τ*(J+1)+k*(S.length-0)+k≤_
  rw [Nat.sub_zero,dates]
  have product:=Nat.mul_le_mul_right ((t+1)*J) active
  have first : τ*(J+1)+k*((t+1)*J)+k≤τ*(J+1)+(κ*(J+1))*((t+1)*J)+κ*(J+1) :=
    Nat.add_le_add (Nat.add_le_add_left product _) active
  apply first.trans
  rw [pow_two]
  nlinarith [Nat.zero_le (τ*J*J),Nat.zero_le (τ*J),Nat.zero_le (κ*J*J), Nat.zero_le (κ*t), Nat.zero_le (κ*J), Nat.zero_le (κ*t*J)]

end Hierarchy.DescentCompiler.AtomSchedule

end OAI

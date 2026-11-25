import OAI.Hierarchy.ProbeStageRecordSpace

namespace OAI
/-! # Address capacity for linear-sized calendar tables -/

namespace Hierarchy.ProtocolRAM.Calendar.GlobalTests
open ProbeStage.Native

/-- The interval counter can accumulate a linear number of bounded commodity
words using the already chosen CT word size, even at the original height z. -/
theorem linear_room (z d C : ℕ) (large : C≤z) : 2^z*C<2^(wordBits z d copies) := by
  have h : C<2^z := large.trans_lt (Nat.lt_two_pow_self (n:=z))
  have lo := Nat.mul_lt_mul_of_pos_left h (Nat.two_pow_pos z)
  rw [←pow_add] at lo
  apply lo.trans_le
  apply Nat.pow_le_pow_right (by decide)
  rw [wordBits_linear]
  omega

end Hierarchy.ProtocolRAM.Calendar.GlobalTests

end OAI

import OAI.Computability.VPVNP.CursorBounds
import OAI.Computability.VPVNP.PrimedInputRAMOpcodeExecutionLayout

/-!
# Private work of the scheduled pair counter

The two input passes use the live address width, and the parser's word guesses use
fourth powers of that width. For a fixed address multiplier their dispatched costs
both fit the auxiliary machine's per-call private-work budget at large lengths.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedCounter.Resources

open Filter BurstRAM PrimedInputRAM.Opcodes

/-- The `n^10` private-work bound includes six elementary operations per instruction
and the fixed dispatch overhead of the full coefficient counter. -/
theorem eventually_privateWork (B : ℕ) :
    ∀ᶠ n : ℕ in atTop, 6 * max (nativeFuel (addressWidth B n) + 20)
      (12 * CursorBounds.wordBits B n + 110) ≤ n^10 := by
  filter_upwards [eventually_ge_atTop (B+10), eventually_ge_atTop (6*197)] with n hB hcost
  have hn : 1 ≤ n := by omega
  have hlog : Nat.clog 2 n ≤ n := (Nat.clog_le_iff_le_pow Nat.one_lt_two).mpr Nat.lt_two_pow_self.le
  have hwidth : addressWidth B n + 10 ≤ n^2 := calc
    addressWidth B n + 10 ≤ B*n + 10*n :=
      Nat.add_le_add (Nat.mul_le_mul_left B hlog) (Nat.le_mul_of_pos_right 10 hn)
    _ = (B+10)*n := (Nat.add_mul ..).symm
    _ ≤ n^2 := by simpa [pow_two] using Nat.mul_le_mul_right n hB
  have hw : CursorBounds.wordBits B n ≤ n^8 := by
    simpa only [CursorBounds.wordBits, CursorBounds.addressBits, ← pow_mul] using Nat.pow_le_pow_left hwidth 4
  have hr := hwidth.trans (Nat.pow_le_pow_right hn (by decide : 2 ≤ 8))
  have hpow : 1 ≤ n^8 := Nat.one_le_pow _ _ hn
  calc
    6 * max _ _ ≤ 6 * (197*n^8) := by
      apply Nat.mul_le_mul_left 6 (max_le _ _)
      · unfold nativeFuel
        omega
      · omega
    _ = (6*197)*n^8 := (Nat.mul_assoc ..).symm
    _ ≤ n*n^8 := Nat.mul_le_mul_right _ hcost
    _ = n^9 := (pow_succ' n 8).symm
    _ ≤ n^10 := Nat.pow_le_pow_right hn (by decide)

end PrimedCounter.Resources

end VPVNP
end Computability
end OAI

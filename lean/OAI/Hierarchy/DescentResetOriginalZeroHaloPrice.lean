import OAI.Hierarchy.DescentResetOriginalZeroHalo
import OAI.Hierarchy.DescentDyadicSpan

namespace OAI
/-! # Size and address range of the original three reset digit tables -/
namespace Hierarchy.DescentResetOriginalZeroHalo

theorem shift (base H G M b : ℕ) :
    endAddress base H G M b = base + endAddress 0 H G M b := by
  simp only [endAddress, Nat.zero_add, Nat.add_assoc]

theorem extent (base H G M b : ℕ) :
    endAddress base H G M b ≤ base + 3 * count H G M b + 2 := by
  have padding : 2 ^ bits H G M b ≤ 2 * (count H G M b + 1) + 1 :=
    DescentDyadicSpan.span_le (count H G M b + 1)
  have populated : 0 < pageSize M b := Nat.mul_pos (Nat.succ_pos M) (Nat.two_pow_pos b)
  unfold endAddress
  unfold count at padding ⊢
  omega

theorem priced (w base H G M b z short haloBits D : ℕ) :
    let pgm := phase w base H G M b z short haloBits D
    pgm.ticks + DescentStaticWordColumn.names pgm.program = 25 * count H G M b + 19 := by
  change 4 + 10 * count H G M b + DescentStaticWordColumn.names
    (DescentStaticWordColumn.program w base (literal H G M b z short haloBits D) (count H G M b)) = _
  rw [DescentStaticWordColumn.names_mount]
  omega

end Hierarchy.DescentResetOriginalZeroHalo

end OAI

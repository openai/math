import OAI.Computability.BorderVNP.RoutingISAPaddingCommon

/-! # Linear time for all incident zero scans -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

/-- Guard and setup ticks for the outer loop and one complete physical scan per partner. -/
def BroadcastFrame.linkCheckTicks (f : BroadcastFrame) (setup extra : ℕ) : ℕ :=
  setup + f.teams * (extra + f.capacity * (zeroScanBody.slots + 1) + 5) + 1

/-- All partner scans together take time linear in the local physical input
length and the number of teams. The estimate charges even the skipped self block. -/
theorem BroadcastFrame.linkCheckTicks_le (f : BroadcastFrame) {w b : ℕ} (fit : f.Fits w b)
    (setup extra : ℕ) :
    f.linkCheckTicks setup extra ≤ (setup + extra + 2 * (zeroScanBody.slots + 1) + 6) *
      (f.processors * f.stride + f.teams + 1) := by
  let input := f.processors * f.stride
  let length := input + f.teams + 1
  let tickCost := zeroScanBody.slots + 1
  have partners : f.teams ≤ 2 * (f.teams - 1) := by have := fit.three; omega
  have exterior : (f.teams - 1) * f.link ≤ f.stride := Nat.le_add_left ..
  have capacity : f.teams * f.capacity ≤ 2 * input := by
    calc
      _ ≤ (2 * (f.teams - 1)) * f.capacity := Nat.mul_le_mul_right _ partners
      _ = 2 * (f.processors * ((f.teams - 1) * f.link)) := by unfold capacity; ring
      _ ≤ 2 * input := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ exterior)
  have one : setup + 1 ≤ (setup + 1) * length :=
    Nat.le_mul_of_pos_right _ (Nat.zero_lt_succ _)
  have perTeam : (extra + 5) * f.teams ≤ (extra + 5) * length :=
    Nat.mul_le_mul_left _ (by dsimp [length]; omega)
  have scan : (f.teams * f.capacity) * tickCost ≤ (2 * tickCost) * length := by
    calc
      _ ≤ (2 * input) * tickCost := Nat.mul_le_mul_right _ capacity
      _ = (2 * tickCost) * input := by ring
      _ ≤ (2 * tickCost) * length := Nat.mul_le_mul_left _ (by dsimp [length]; omega)
  calc
    f.linkCheckTicks setup extra =
        (setup + 1) + (extra + 5) * f.teams + (f.teams * f.capacity) * tickCost := by
      unfold linkCheckTicks
      dsimp only [tickCost]
      ring
    _ ≤ (setup + 1) * length + (extra + 5) * length + (2 * tickCost) * length :=
      Nat.add_le_add (Nat.add_le_add one perTeam) scan
    _ = _ := by change _ = (setup + extra + 2 * tickCost + 6) * length; ring

end RoutingISA

end BorderVNP
end Computability
end OAI

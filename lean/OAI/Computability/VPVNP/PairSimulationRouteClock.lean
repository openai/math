import OAI.Computability.VPVNP.RAMApplications
import OAI.Computability.VPVNP.CursorFieldOffsets

/-!
# Clock for the native cursor routing checks

The scheduler visits one successor field per cursor bit and at most one sort
field per phase and step. Each resident word takes at most thirteen ticks.
The processor's bounds on bucket size and word width put the entire scan,
including its field setup and final decision, within the stated clock.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.RouteClock

open BurstRAM RAMLayout

/-- The successor loop, nested sort loop and final decision fit within the
routing allowance on both live and virtual processors. -/
theorem scheduler_le {n D e w : ℕ} (budget : ProcessorBudget n D e w) (hn : 2048 ≤ n) :
    (13 * (8 * w) + 37) * D + 2 + (((13 * blockBits (2 ^ e) w + 37) * D + 5) * D + 2) + 4 ≤
      n ^ 5 := by
  have hd : D ≤ n := by have h := budget.phase_le; omega
  have hw := budget.word_le
  have hH := budget.bucket_le
  have hb : blockBits (2 ^ e) w ≤ 40 * n ^ 2 := calc
    _ ≤ 4 * (2 * n) * 5 * n := by unfold blockBits; gcongr
    _ = _ := by ring
  have pos : 0 < n := by omega
  have hn1 : 1 ≤ n ^ 4 := Nat.one_le_pow _ _ pos
  have hn2 : n ≤ n ^ 4 := Nat.le_self_pow (by decide) n
  have hn3 : n ^ 2 ≤ n ^ 4 := Nat.pow_le_pow_right pos (by decide)
  calc
    _ ≤ (13 * (8 * n) + 37) * n + 2 + (((13 * (40 * n ^ 2) + 37) * n + 5) * n + 2) + 4 := by
      gcongr
    _ = 520 * n ^ 4 + 141 * n ^ 2 + 42 * n + 8 := by ring
    _ ≤ 711 * n ^ 4 := by omega
    _ ≤ n ^ 5 := by rw [pow_succ' n 4]; exact Nat.mul_le_mul_right _ (by omega)

end PairSimulation.RouteClock

end VPVNP
end Computability
end OAI

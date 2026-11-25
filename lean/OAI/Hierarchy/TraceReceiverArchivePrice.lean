import OAI.Hierarchy.TraceReceiverForest
import OAI.ThreeFlat.Diagonal.PhysicalSelectedClock

namespace OAI
/-! # Instruction rates of the native stage and receiver's terminal pin maps -/

noncomputable section
namespace Hierarchy.TraceFactorReceiver.Gather

open ThreeFlat Diagonal RAM
variable {F : Type} [Field F] [Fintype F]

/-- The original selected RAM's combined stage and terminal charge fits the
two extra coefficients of the current per-root work price. The finite block
rate covers the seed ROM, motif and guard programs, all stage joins, and
page instructions. The terminal rate is that of the actual pin-map ROM. -/
theorem native_archive_price (B : PhysicalStage.Block F) (u degree coefficient : ℕ)
    (positive : 0<coefficient) :
    let stages := (B.repeat (u^8)).length
    B.archiveUnit u coefficient degree ≤
      (setupPrice stages B.stageClockRate+mapPrice degree TickTerminalRoot.rootFactor)*
        B.terminalRowRate u coefficient := by
  intro stages
  exact archive_price stages degree B.stageClockRate TickTerminalRoot.rootFactor
    (coefficient*(16*u^10+1)^3) (Nat.mul_pos positive (by positivity))

/-- Combining these additional rates preserves the original per-tree replay
and contraction allowance, including both outer-loop constants per root. -/
theorem native_with_replay (B : PhysicalStage.Block F) (u depth degree coefficient : ℕ)
    (positive : 0<coefficient) :
    let stages := (B.repeat (u^8)).length
    (10025+1016*depth)*B.terminalRowRate u coefficient+B.archiveUnit u coefficient degree ≤
      (10025+1016*depth+setupPrice stages B.stageClockRate+mapPrice degree TickTerminalRoot.rootFactor)*
        B.terminalRowRate u coefficient := by
  intro stages
  have cost := Nat.add_le_add_left (native_archive_price B u degree coefficient positive)
    ((10025+1016*depth)*B.terminalRowRate u coefficient)
  simpa only [Nat.add_mul,Nat.add_assoc] using cost

end Hierarchy.TraceFactorReceiver.Gather
end

end OAI

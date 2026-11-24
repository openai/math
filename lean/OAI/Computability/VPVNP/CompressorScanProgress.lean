import OAI.Computability.VPVNP.CompressorRefreshStageFrame
import OAI.Computability.VPVNP.CompressorSourceOnline

/-!
# Scheduler guard progress of a finite ordinal scan

When the exclusive stop fits in a word, every natural strict inequality
in the source trace is the same inequality tested by the scheduler.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords

open BurstRAM
open scoped Fin.CommRing

theorem StageFrame.Scanned.toProgress {w first N : ℕ} {rs : List (Report w)}
    (shape : StageFrame.Scanned first N rs) (fit : N < 2^w) :
    SourceOnline.Progress (N : Word w) (first : Word w) rs := by
  induction shape with
  | done => exact .done le_rfl
  | @next j N rep tail live returned scanned ih =>
    have active : (j : Word w) < (N : Word w) := by
      change j % 2^w < N % 2^w
      rwa [Nat.mod_eq_of_lt (live.trans fit), Nat.mod_eq_of_lt fit]
    exact .next active returned (ih fit)

end CompressorRecords

end VPVNP
end Computability
end OAI

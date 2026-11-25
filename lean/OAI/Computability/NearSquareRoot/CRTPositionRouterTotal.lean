import OAI.Computability.NearSquareRoot.CRTPositionRouter
import OAI.Computability.NearSquareRoot.CRTPositionCommandTotal

/-! # Termination and correctness of every generated router -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PositionProgram
open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
open IntegerMultiplication.Adic IntegerMultiplication.Loom

/-- The same command whose time and space are controlled by `routeCmd_runs`
returns the correct permutation for every pair of guessed reserve degrees. -/
theorem routeCmd_total {ρ : ℝ} {rect : Cmd} (positive : 0 ≤ ρ)
    (ready : Effective.rectContract rect ρ) (a b : ℕ) {I : Type} (k : I → ℕ)
    {U : I → Type} (u : (i : I) → Series (U i)) (pos : ∀ i, 0 < (u i).count)
    (p : (i : I) → Equiv.Perm (Fin (k i))) (f : (i:I) → Block 2 (k i) → U i → Bead) :
    ∃ t, EffectiveTask.Runs (routeCmd a b rect) t
      (together (fun i => send (Reflections.table (p i))) (cloth (fun i => line 2 (k i)) u f))
      (cloth (fun i => line 2 (k i)) u (fun i z => f i (flatBitPullback (p i) z))) :=
  PositionCmd.position_raw_runs (PositionRows.RowCommand.rawGroupedTable positive
    (opcodeCmd_runs positive ready)) a b k u pos p f

end Controlled.PositionProgram

end NearSquareRoot
end Computability
end OAI

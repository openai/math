import OAI.Computability.VPVNP.QueryControl

/-!
# Traversal time for a payload query

The rightward scan stops on the blank after the entire input. The leftward scan
then counts down to phase one, when the selected payload bit is under the head.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace QueryMachine

open UniversalMachine TableCompiler QueryTape

variable {k : ℕ} {Q : Type*} [Fintype Q] (p : QueryProgram k Q) (t : ℕ) (input : Word)
  {r : Fin (t + 1)} {q : Q} {i : Fin k} {low high : Q}

/-- Phase zero scans each remaining input bit in one transition. -/
theorem scanRight (hr : r.val ≠ 0) (h : p.step q = .read i low high)
    (pos dist budget : ℕ) (hend : pos + dist = input.length) :
    countAt p t input pos (r, q, 0) (dist + budget) =
      countAt p t input input.length (r, q, 0) budget := by
  induction dist generalizing pos with
  | zero => simpa using congrArg (fun j => countAt p t input j (r, q, 0) budget) hend
  | succ dist ih =>
    have hpos : pos < input.length := by omega
    have hbit : (atPosition input pos).head ≠ 0 := by
      rw [head_atPosition_of_lt _ _ hpos]
      split <;> decide
    have hcommand : command p t (r, q, 0) (atPosition input pos).head =
        .move (r, q, 0) 2 := by simp [command, h, hr, hbit]
    rw [Nat.succ_add, countAt_step, hcommand]
    change paths (machine p t) (dist + budget)
      (running (start p t) (r, q, 0) ((atPosition input pos).move .right) _) = _
    rw [move_right_atPosition]
    exact ih (pos + 1) (by omega)

/-- Each left move lowers the phase counter by one until the read phase. -/
theorem scanLeft (hr : r.val ≠ 0) (h : p.step q = .read i low high)
    (base rem budget : ℕ) (hrem : rem + 1 < k + 1) :
    countAt p t input (base + rem) (r, q, ⟨rem + 1, hrem⟩) (rem + budget) =
      countAt p t input base (r, q, ⟨1, by omega⟩) budget := by
  induction rem with
  | zero => simp
  | succ rem ih =>
    have hprev : rem + 1 < k + 1 := by omega
    have hcommand (a : Symbol) : command p t (r, q, ⟨rem.succ + 1, hrem⟩) a =
        .move (r, q, ⟨rem + 1, hprev⟩) 1 := by
      simp [command, h, hr, predFin]
    rw [Nat.succ_add rem budget, countAt_step, hcommand]
    change paths (machine p t) (rem + budget)
      (running (start p t) (r, q, ⟨rem + 1, hprev⟩)
        ((atPosition input ((base + rem) + 1)).move .left) _) = _
    rw [move_left_atPosition_succ]
    exact ih hprev

end QueryMachine

end VPVNP
end Computability
end OAI

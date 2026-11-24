import OAI.Computability.VPVNP.RAMTapeISAPorts
import OAI.Computability.VPVNP.StructuredStackLoop

/-! # Trimming an endpoint's allocated word

Each unary count mark removes one zero from the front of the allocated word.
The empty count ends the scan, leaving the remaining word in its original order.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SiteEndpointTrim

open Function Routine

variable {K : Type}

private def popZero (dst : K) :=
  popCase dst (halt false) ret (halt false)

/-- Trim one leading zero from the destination per unary count mark, rejecting malformed marks
or destination bits. -/
def routine (count dst : K) : FiniteRoutine K :=
  .ofRoutine (popLoop count (fun _ => true) (halt false) (popZero dst))

/-- Removing each zero costs a count pop, a word pop, and a return. One
final empty count pop terminates the loop. Only the two named stacks change. -/
theorem run [DecidableEq K] {count dst : K} (hne : count ≠ dst) (s : Stacks K)
    (n : ℕ) (tail : List Bool) (hc : s count = List.replicate n true)
    (hd : s dst = List.replicate n false ++ tail) :
    (routine count dst).Runs (3*n+1) s (update (update s count []) dst tail) := by
  induction n generalizing s with
  | zero =>
    change s count = [] at hc
    change s dst = tail at hd
    rw [← hc, update_eq_self, ← hd, update_eq_self]
    exact Runs.popLoop_empty count (fun _ => true) (halt false) (popZero dst) hc
  | succ n ih =>
    rw [List.replicate_succ] at hc
    rw [List.replicate_succ, List.cons_append] at hd
    let popped := update s count (List.replicate n true)
    let mid := update popped dst (List.replicate n false ++ tail)
    have hword : popped dst = false :: (List.replicate n false ++ tail) :=
      (update_of_ne hne.symm ..).trans hd
    have body := runs_popCase_false dst (halt false) ret (halt false) hword (runs_ret mid)
    have rest := ih mid (by simp [mid, popped, update_of_ne hne]) (update_self ..)
    have steps := Runs.popLoop_true_continue count (fun _ => true) (halt false) (popZero dst)
      hc rfl body rest
    have endState : update (update mid count []) dst tail = update (update s count []) dst tail := by
      simp only [mid, popped, update_comm hne.symm, update_idem]
    rw [endState] at steps
    exact (show 1+(1+1)+(3*n+1) = 3*(n+1)+1 by omega) ▸ steps

end RAMTape.SiteEndpointTrim

end VPVNP
end Computability
end OAI

import OAI.Computability.VPVNP.RAMTapeISAPorts
import OAI.Computability.VPVNP.StructuredStackLoop

/-!
# A finite-control counted scan of a coefficient stream

The register bank holds a stack of one-bit markers. Each marker causes one
normal execution of the same body. The body can update the accumulator and
advance all coefficient streams. The empty marker stack returns to the caller.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.FiniteRoutine

variable {K : Type}

/-- Execute the body on each true marker, stopping normally on an empty stack. -/
def repeatMarked (marker : K) (body : FiniteRoutine K) : FiniteRoutine K :=
  ofRoutine (Routine.popLoop marker (fun _ => true) (Routine.halt false) body.body)

/-- A fold over a represented stream uses at most one bounded body run and
one marker pop per item, plus the final test for the empty marker stack. -/
theorem repeatMarked_runs [DecidableEq K] {α β : Type*} (marker : K)
    (body : FiniteRoutine K) (frame : List α → β → Stacks K)
    (step : β → α → β) (cap : ℕ)
    (hmarks : ∀ xs b, frame xs b marker = List.replicate xs.length true)
    (hstep : ∀ a xs b, ∃ t ≤ cap, body.Runs t
      (Function.update (frame (a :: xs) b) marker (List.replicate xs.length true))
      (frame xs (step b a)))
    (xs : List α) (b : β) :
    ∃ t ≤ xs.length * (cap + 1) + 1, (repeatMarked marker body).Runs t
      (frame xs b) (frame [] (xs.foldl step b)) := by
  induction xs generalizing b with
  | nil =>
    refine ⟨1, by simp, ?_⟩
    exact Routine.Runs.popLoop_empty marker (fun _ => true) (Routine.halt false) body.body (s := frame [] b) (hmarks [] b)
  | cons a xs ih =>
    obtain ⟨u, hu, hbody⟩ := hstep a xs b
    obtain ⟨v, hv, htail⟩ := ih (step b a)
    refine ⟨1 + u + v, ?_, ?_⟩
    · simp only [List.length_cons, Nat.succ_mul]
      omega
    · exact Routine.Runs.popLoop_true_continue marker (fun _ => true) (Routine.halt false) body.body
        (by rw [hmarks, List.length_cons, List.replicate_succ]) rfl hbody htail

end RAMTape.FiniteRoutine

end VPVNP
end Computability
end OAI

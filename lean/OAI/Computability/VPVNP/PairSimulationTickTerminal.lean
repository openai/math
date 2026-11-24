import OAI.Computability.VPVNP.PrimedCounterGuessWord

/-!
# Uniqueness of the tick count at a terminal instruction

Starting at the same native configuration, two runs consisting entirely of
local ticks take the same number of ticks to reach a terminal instruction.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedCounter.GuessWord.Prefix

open BurstRAM PrivateRAM

variable {w p r k n m : ℕ} {M : Machine w p r k} {c d e : Config w p r}

private theorem ticks_unique_of_no_local
    (run : Prefix M c (List.replicate n .tick) d)
    (other : Prefix M c (List.replicate m .tick) e)
    (hd : ∀ next, M.program.step d ≠ .localStep next)
    (he : ∀ next, M.program.step e ≠ .localStep next) : n = m ∧ d = e := by
  induction n generalizing c m with
  | zero =>
    cases run
    cases m with
    | zero => cases other; exact ⟨rfl, rfl⟩
    | succ m =>
      rw [List.replicate_succ] at other
      cases other with
      | tick step _ => exact (hd _ step).elim
  | succ n ih =>
    rw [List.replicate_succ] at run
    cases run with
    | tick step tail =>
      cases m with
      | zero => cases other; exact (he _ step).elim
      | succ m =>
        rw [List.replicate_succ] at other
        cases other with
        | tick step' tail' =>
          cases CallAction.localStep.inj (step.symm.trans step')
          obtain ⟨hlen, hout⟩ := ih tail tail'
          exact ⟨congrArg Nat.succ hlen, hout⟩

/-- Two tick prefixes from one configuration that end in rejection or a
finished call have the same length and the same terminal configuration. -/
theorem ticks_terminal_unique
    (run : Prefix M c (List.replicate n .tick) d)
    (other : Prefix M c (List.replicate m .tick) e)
    (hd : M.program.step d = .reject ∨ ∃ result, M.program.step d = .finish result)
    (he : M.program.step e = .reject ∨ ∃ result, M.program.step e = .finish result) :
    n = m ∧ d = e := by
  apply ticks_unique_of_no_local run other
  · rcases hd with h | ⟨result, h⟩ <;> simp [h]
  · rcases he with h | ⟨result, h⟩ <;> simp [h]

end PrimedCounter.GuessWord.Prefix

end VPVNP
end Computability
end OAI

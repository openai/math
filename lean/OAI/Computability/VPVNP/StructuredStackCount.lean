import OAI.Computability.VPVNP.StructuredStacks

/-! # Continuation counts after deterministic stack runs -/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.Routine

variable {K Q : Type*} [DecidableEq K]

private theorem countFrom_runs (r : Routine K Q) {q q' : Option Q} {s out : Stacks K} {n : ℕ}
    (h : StackRuns r.standalone n q s q' out) (c : ℕ → Stacks K → ℕ) (fuel : ℕ) :
    r.countFrom c (fuel+n) q s = r.countFrom c fuel q' out := by
  induction h with
  | nil => rfl
  | @cons q₀ _ _ _ _ _ _ hs _ ih =>
    cases q₀ with
    | none => cases hs <;> simp [standalone, close] at *
    | some q =>
      cases hs with
      | push h =>
        simp only [standalone, close] at h
        simp only [countFrom, h]
        exact ih
      | pop h =>
        simp only [standalone, close] at h
        simp only [countFrom, h]
        exact ih
      | goto h =>
        simp only [standalone, close] at h
        simp only [countFrom, h]
        exact ih

/-- A deterministic run to a normal return invokes the continuation once,
with exactly the run length deducted from the available budget. -/
theorem Runs.count_eq {r : Routine K Q} {n : ℕ} {s out : Stacks K} (h : r.Runs n s out)
    (c : ℕ → Stacks K → ℕ) (fuel : ℕ) : r.count c (fuel + n) s = c fuel out :=
  (countFrom_runs r h c fuel).trans (countFrom_none ..)

end RAMTape.Routine

end VPVNP
end Computability
end OAI

import OAI.Computability.VPVNP.StructuredStacks

/-! # Using an existing finite stack program as a returning routine

The distinguished halt of a legacy program becomes a normal return to the caller.
A deterministic execution ending at that halt has exactly the same length after
installation, provided it starts outside the return state.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.Routine

variable {K Q : Type*} [DecidableEq Q]

/-- Redirect transitions entering the normal completion state to the caller. -/
def ofCode (code : StackCode K Q) (entry done : Q) : Routine K Q where
  entry := entry
  code q := if q = done then .goto none else
    (code q).rename id (fun q' => if q' = done then none else some q')

theorem runs_ofCode [DecidableEq K] {code : StackCode K Q} {entry done : Q}
    {t : ℕ} {s out : Stacks K} (hentry : entry ≠ done) (hdone : (code done).returns = true)
    (run : StackRuns code t entry s done out) : (ofCode code entry done).Runs t s out := by
  let labels (q : Q) : Option Q := if q = done then none else some q
  let target := (ofCode code entry done).standalone
  have hc (q : Q) (hq : (code q).returns = false) : target (labels q) = (code q).rename id labels := by
    have hne : q ≠ done := fun h => by subst q; exact Bool.noConfusion (hdone.symm.trans hq)
    simp [target, standalone, close, ofCode, labels, hne]
  have hi (st : Stacks K) : installStacks id s st = st := by
    funext k
    exact installStacks_at Function.injective_id s st k
  change StackRuns target t (some entry) s none out
  simpa only [labels, ite_eq_right hentry, ite_eq_left rfl, hi] using
    run.lift id Function.injective_id labels s hc

end RAMTape.Routine

end VPVNP
end Computability
end OAI

import OAI.Computability.VPVNP.StructuredStacks

/-! # Executing a structured routine inside its caller

Installed instructions keep the same stack labels. The last ordinary
instruction returns directly to the caller's continuation.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.Routine

variable {K Q R : Type*} [DecidableEq K]

/-- A deterministic run transfers to its caller without changing its cost. -/
theorem Runs.link {inner : Routine K Q} {t : ℕ} {s out : Stacks K}
    (run : inner.Runs t s out) (outer : Routine K R) (label : Q → R) (resume : Option R)
    (h : ∀ q, outer.code (label q) = inner.install label resume q) :
    StackRuns outer.standalone t (some (label inner.entry)) s resume out := by
  let labels (q : Option Q) := q.elim resume (some ∘ label)
  have hc (q : Option Q) (hq : (inner.standalone q).returns = false) :
      outer.standalone (labels q) = (inner.standalone q).rename id labels := by
    cases q with
    | none => contradiction
    | some q => exact h q
  have hi (st : Stacks K) : installStacks id s st = st := by
    funext k
    exact installStacks_at Function.injective_id s st k
  simpa only [labels, Option.elim_none, Option.elim_some, Function.comp_apply, hi] using
    run.lift id Function.injective_id labels s hc

end RAMTape.Routine

end VPVNP
end Computability
end OAI

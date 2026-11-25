import OAI.Computability.BorderVNP.RoutingISANatural

/-!
# Counted loops in the finite word evaluator

The converse invariant applies even when the loop body has rejecting branches.
Every successful loop history satisfies the checked exit condition.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

open VPVNP.BurstRAM

variable {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}

/-- Any returned history of a loop preserves every invariant preserved by
successful body executions and leaves its actual guard false. -/
theorem Runs.while_invariant {c : Code} {s m es t mt} (run : Runs pub macros c s m es t mt)
    (cursor bound : Reg) (body : Code) (Inv : Bank w → Memory w → Prop)
    (step : ∀ {s m es t mt}, Inv s m → s cursor < s bound →
      Runs pub macros body s m es t mt → Inv t mt)
    (same : c = .whileLt cursor bound body) (init : Inv s m) :
    Inv t mt ∧ ¬ t cursor < t bound := by
  induction run with
  | atom ha _ _ => subst same; cases ha
  | seq | ifEq | ifLt | choose => contradiction
  | whileDone guard => cases same; exact ⟨init,guard⟩
  | whileStep guard first loop ih₁ ih₂ =>
    cases same
    exact ih₂ rfl (step init guard first)

end RoutingISA

end BorderVNP
end Computability
end OAI

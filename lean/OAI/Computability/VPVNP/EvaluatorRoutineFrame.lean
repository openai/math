import OAI.Computability.VPVNP.RAMTapeRoutinePorts

/-! # Framing nondeterministic evaluator callbacks

Renaming a returning routine into a larger bank of stacks leaves every other
stack available to the scheduler. Each binary choice retains its two slots,
and the continuation receives the residual fuel on that particular path.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.FiniteRoutine

variable {K L : Type} [DecidableEq K] [DecidableEq L]

/-- Exact continuation semantics on a disjoint set of named ports. -/
theorem countFrom_onPorts (r : FiniteRoutine K) (ports : K → L) (hp : Function.Injective ports)
    (base : Stacks L) (c : ℕ → Stacks L → ℕ) (n : ℕ) (q : Option r.State) (s : Stacks K) :
    (r.onPorts ports).body.countFrom c n q (installStacks ports base s) =
      r.body.countFrom (fun fuel out => c fuel (installStacks ports base out)) n q s := by
  induction n generalizing q s with
  | zero => cases q <;> rfl
  | succ n ih =>
    cases q with
    | none => rfl
    | some q =>
      simp only [Routine.countFrom]
      have hcode : (r.onPorts ports).body.code q = (r.body.code q).rename ports id := rfl
      rw [hcode]
      cases r.body.code q <;> simp [installStacks_at hp, installStacks_update hp, ih]

/-- The entry point of a framed routine can be invoked from an arbitrary caller state. -/
theorem count_onPorts (r : FiniteRoutine K) (ports : K → L) (hp : Function.Injective ports)
    (base : Stacks L) (c : ℕ → Stacks L → ℕ) (n : ℕ) :
    (r.onPorts ports).body.count c n base =
      r.body.count (fun fuel out => c fuel (installStacks ports base out)) n (base ∘ ports) := by
  have h := countFrom_onPorts r ports hp base c n (some r.body.entry) (base ∘ ports)
  rwa [installStacks_eq hp base (base ∘ ports) (fun _ => rfl)] at h

end RAMTape.FiniteRoutine

end VPVNP
end Computability
end OAI

import OAI.Computability.VPVNP.RAMTapeRoutinePorts
import OAI.Computability.VPVNP.StructuredStackTotal

/-!
# All-branch stopping bounds for framed stack routines

Installing an injective port map preserves each stack transition and both branches of every
choice. The same residual fuel is passed to the continuation, with the local outputs written
back into the caller's untouched frame.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.FiniteRoutine

variable {K L : Type} [DecidableEq K] [DecidableEq L]

/-- Transport the continuation predicate through the installed ports, at any control label. -/
theorem allStopsFrom_onPorts (r : FiniteRoutine K) (ports : K → L) (hp : Function.Injective ports)
    (base : Stacks L) (c : ℕ → Stacks L → Prop) (n : ℕ) (q : Option r.State) (s : Stacks K) :
    (r.onPorts ports).body.AllStopsFrom c n q (installStacks ports base s) ↔
      r.body.AllStopsFrom (fun fuel out => c fuel (installStacks ports base out)) n q s := by
  induction n generalizing q s with
  | zero => cases q <;> rfl
  | succ n ih =>
    cases q with
    | none => rfl
    | some q =>
      simp only [Routine.AllStopsFrom]
      have hcode : (r.onPorts ports).body.code q = (r.body.code q).rename ports id := rfl
      rw [hcode]
      cases r.body.code q <;> simp [installStacks_at hp, installStacks_update hp, ih]

/-- The local machine starts with exactly the caller's stacks at its named ports. -/
theorem allStops_onPorts (r : FiniteRoutine K) (ports : K → L) (hp : Function.Injective ports)
    (base : Stacks L) (c : ℕ → Stacks L → Prop) (n : ℕ) :
    (r.onPorts ports).body.AllStops c n base ↔
      r.body.AllStops (fun fuel out => c fuel (installStacks ports base out)) n (base ∘ ports) := by
  have h := allStopsFrom_onPorts r ports hp base c n (some r.body.entry) (base ∘ ports)
  rwa [installStacks_eq hp base (base ∘ ports) (fun _ => rfl)] at h

end RAMTape.FiniteRoutine

end VPVNP
end Computability
end OAI

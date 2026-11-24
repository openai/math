import OAI.Computability.VPVNP.RankQueryGramReadSpace
import OAI.Computability.VPVNP.EvaluatorRadixSpace

/-! # Lifting a bounded local trace at a known call boundary -/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.FiniteRoutine

open UniversalCountStack

variable {K L : Type} [DecidableEq K] [DecidableEq L]

private theorem same_endpoint {Q : Type} {code : StackCode K Q} {n : ℕ}
    {q u v : Q} {s out out' : Stacks K} (a : StackRuns code n q s u out) (b : StackRuns code n q s v out') :
    u = v ∧ out = out' := by
  induction a with
  | nil => cases b; exact ⟨rfl,rfl⟩
  | cons h _ ih =>
    cases b with
    | cons h' tail =>
      have unique {q₀ q₁ q₂ : Q} {s₀ s₁ s₂ : Stacks K}
          (hh : StackStep code q₀ s₀ q₁ s₁) (hh' : StackStep code q₀ s₀ q₂ s₂) : q₁ = q₂ ∧ s₁ = s₂ := by
        cases hh <;> cases hh' <;> simp_all
      obtain ⟨rfl,rfl⟩ := unique h h'
      exact ih tail

/-- Returning deterministic calls have a unique length and final bank. -/
theorem return_unique {r : FiniteRoutine K} {t n : ℕ} {s a b : Stacks K}
    (h : r.Runs t s a) (g : r.Runs n s b) : t = n ∧ a = b := by
  have he := Nat.le_antisymm (EvaluatorRadixDivision.ticks_le_at_return g rfl h)
    (EvaluatorRadixDivision.ticks_le_at_return h rfl g)
  subst n
  exact ⟨rfl,(same_endpoint h g).2⟩

/-- Lift a space certificate onto an already verified caller trace. Equality
of normal returns identifies its actual final scratch state and elapsed time. -/
theorem BoundedRun.lift_trace {r : FiniteRoutine K} {ports : K → L} (hp : Function.Injective ports)
    {cap n t : ℕ} {s u : Stacks L} {small out : Stacks K} (run : r.BoundedRun cap n small out)
    (outer : (r.onPorts ports).Runs t s u)
    (start : ∀ j, (s j).length ≤ cap) (hin : ∀ i, s (ports i) = small i) :
    (r.onPorts ports).BoundedRun cap t s u := by
  have h := run.onPorts hp s (fun j _ => start j)
  rw [installStacks_frame hp hin (fun _ _ => rfl)] at h
  obtain ⟨rfl,he⟩ := return_unique h.runs outer
  rwa [← he]

end RAMTape.FiniteRoutine

end VPVNP
end Computability
end OAI

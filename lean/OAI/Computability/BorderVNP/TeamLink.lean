import OAI.Computability.BorderVNP.TeamPrivateFragment

/-! # Installing deterministic and choice-tracked stack fragments in the team validator -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamLink

open VPVNP.RAMTape TeamPrivateFragment

variable {K L Q R : Type} [DecidableEq K] [DecidableEq L]

/-- A normal return from an installed finite routine enters the caller's continuation at
the same clock tick. Ports outside the embedding retain their contents. -/
theorem routine {rt : FiniteRoutine K} {t : ℕ} {s out : Stacks K} (run : rt.Runs t s out)
    (target : StackCode L R) (ports : K → L) (hp : Function.Injective ports) (label : rt.State → R)
    (resume : R) (base : Stacks L)
    (rows : ∀ q, target (label q) = (rt.body.code q).rename ports (fun next => next.elim resume label)) :
    StackRuns target t (label rt.body.entry) (installStacks ports base s) resume (installStacks ports base out) := by
  have h := run.lift ports hp (fun q => q.elim resume label) base (by
    rintro (_ | q) hc
    · contradiction
    · exact rows q)
  exact h

/-- Link a same-port routine without changing its stack representation. -/
theorem routine_id {rt : FiniteRoutine K} {t : ℕ} {s out : Stacks K} (run : rt.Runs t s out)
    (target : StackCode K R) (label : rt.State → R) (resume : R)
    (rows : ∀ q, target (label q) = (rt.body.code q).rename id (fun next => next.elim resume label)) :
    StackRuns target t (label rt.body.entry) s resume out := by
  have e (z : Stacks K) : installStacks id s z = z := funext fun i => installStacks_at Function.injective_id s z i
  simpa only [e] using routine run target id Function.injective_id label resume s rows

/-- A fragment replay can be embedded in a larger nondeterministic machine with precisely
the same consumed choice prefix, including when its normal halt becomes a continuation. -/
theorem replay_lift {src : StackCode K Q} {t q bs s q' rest out}
    (run : StackRuns (replay src) t (q,bs) s (q',rest) out)
    (target : StackCode L R) (ports : K → L) (hp : Function.Injective ports) (labels : Q → R) (base : Stacks L)
    (rows : ∀ q, (src q).returns = false → target (labels q) = (src q).rename ports labels) :
    StackRuns (replay target) t (labels q,bs) (installStacks ports base s) (labels q',rest) (installStacks ports base out) := by
  let rename (p : Q × List Bool) := (labels p.1, p.2)
  apply run.lift ports hp rename base
  rintro ⟨q, bs⟩ h
  have hc : (src q).returns = false := by
    cases hs : src q <;> first | rfl | simp [replay, hs] at h
  rw [show rename (q,bs) = (labels q,bs) from rfl, replay, rows q hc, replay]
  cases hs : src q <;> simp only [StackOp.rename, Function.comp_def, rename, id_eq]
  cases bs <;> simp; split <;> rfl

end TeamLink

end BorderVNP
end Computability
end OAI

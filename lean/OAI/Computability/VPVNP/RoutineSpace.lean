import OAI.Computability.VPVNP.RAMTapeRoutinePorts
import OAI.Computability.VPVNP.SpaceRunMonotone

/-! # Preserving stack space across nested calls

Installation, returning calls and sequential composition reuse the same bit-stack
space bound. They can therefore compose exponentially long subroutines without
adding their running times to the caller's space use.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace UniversalCountStack

open RAMTape

variable {K L Q R : Type*} [DecidableEq K] [DecidableEq L]

theorem SpaceRun.initial_cap {code : StackCode K Q} {cap n q s t u} (run : SpaceRun code cap n q s t u) :
    ∀ k, (s k).length ≤ cap := by cases run <;> assumption

theorem SpaceRun.final_cap {code : StackCode K Q} {cap n q s t u} (run : SpaceRun code cap n q s t u) :
    ∀ k, (u k).length ≤ cap := by induction run <;> assumption

/-- Lift control and ports without changing the number of steps or the cap, provided
all caller stacks outside the installed bank already lie below the cap. -/
theorem SpaceRun.lift {src : StackCode K Q} {target : StackCode L R} {cap n q s t u}
    (run : SpaceRun src cap n q s t u) (ports : K → L) (hp : Function.Injective ports)
    (labels : Q → R) (base : Stacks L) (hbase : ∀ l, (∀ k, ports k ≠ l) → (base l).length ≤ cap)
    (hc : ∀ v, (src v).returns = false → target (labels v) = (src v).rename ports labels) :
    SpaceRun target cap n (labels q) (installStacks ports base s) (labels t) (installStacks ports base u) := by
  have installed (v : Stacks K) (h : ∀ k, (v k).length ≤ cap) (l : L) :
      (installStacks ports base v l).length ≤ cap := by
    by_cases hm : ∃ k, ports k = l
    · obtain ⟨k, rfl⟩ := hm
      simpa only [installStacks_at hp] using h k
    · rw [installStacks_outside _ _ (not_exists.mp hm)]
      exact hbase l (not_exists.mp hm)
  induction run with
  | nil _ _ hs => exact .nil _ _ (installed _ hs)
  | cons hs step _ ih => exact .cons (installed _ hs) (step.lift ports hp labels base hc) ih

theorem SpaceRun.linkRoutine {inner : Routine K Q} {cap n : ℕ} {s out : Stacks K}
    (run : SpaceRun inner.standalone cap n (some inner.entry) s none out)
    (outer : Routine K R) (label : Q → R) (resume : Option R)
    (h : ∀ q, outer.code (label q) = inner.install label resume q) :
    SpaceRun outer.standalone cap n (some (label inner.entry)) s resume out := by
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
    run.lift id Function.injective_id labels s (fun l outside ↦ (outside l rfl).elim) hc

end UniversalCountStack

namespace RAMTape.FiniteRoutine

open UniversalCountStack

variable {K L : Type} [DecidableEq K] [DecidableEq L]

/-- Execution of a standalone routine from entry to return in exactly `n` steps with every
stack height bounded by `cap`. -/
abbrev BoundedRun (r : FiniteRoutine K) (cap n : ℕ) (s out : Stacks K) :=
  SpaceRun r.body.standalone cap n (some r.body.entry) s none out

theorem BoundedRun.followedBy {a b : FiniteRoutine K} {cap m n : ℕ} {s t u : Stacks K}
    (ha : a.BoundedRun cap m s t) (hb : b.BoundedRun cap n t u) :
    (a.followedBy b).BoundedRun cap (m+n) s u :=
  (ha.linkRoutine (a.body.followedBy b.body) Sum.inl (some (.inr b.body.entry)) (fun _ ↦ rfl)).trans
    (hb.linkRoutine (a.body.followedBy b.body) Sum.inr none (fun _ ↦ rfl))

theorem BoundedRun.onPorts {a : FiniteRoutine K} {ports : K → L} (hp : Function.Injective ports)
    (base : Stacks L) {cap n : ℕ} {s out : Stacks K} (h : a.BoundedRun cap n s out)
    (hbase : ∀ l, (∀ k, ports k ≠ l) → (base l).length ≤ cap) :
    (a.onPorts ports).BoundedRun cap n (installStacks ports base s) (installStacks ports base out) := by
  exact h.lift ports hp id base hbase (fun q _ ↦ by cases q <;> rfl)

end RAMTape.FiniteRoutine

end VPVNP
end Computability
end OAI

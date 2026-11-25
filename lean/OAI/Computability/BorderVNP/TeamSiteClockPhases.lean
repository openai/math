import OAI.Computability.BorderVNP.TeamSiteTrustedClock

/-! # Processor initialization before any private call

The endpoint startup is entered only from the physical prelude. Once a site starts
its RAM loop, its deterministic steps and its signed choices cannot re-enter the
startup. Thus replacing the private-call rows preserves the existing physical
initialization proof, even for a prelude whose exact internal labels were hidden.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite.TrustedClock

open VPVNP RAMTape BurstRAM

variable {K J Q S : Type}

/-- Predicate on all successor labels of one instruction, for both values of every
choice and all possible symbols read by a pop. -/
def successors (good : Q → Prop) : StackOp K Q → Prop
  | .push _ _ q | .goto q => good q
  | .pop _ f => ∀ b, good (f b)
  | .choose l r => good l ∧ good r
  | .halt _ => True

private theorem successor_rename (ports : K → J) (labels : Q → S) (good : S → Prop)
    (op : StackOp K Q) : successors good (op.rename ports labels) ↔ successors (good ∘ labels) op := by
  cases op <;> rfl

private theorem all_successors (ports : K → J) (labels : Q → S) {good : S → Prop} (h : ∀ q, good (labels q))
    (op : StackOp K Q) : successors good (op.rename ports labels) := by
  rw [successor_rename]
  cases op <;> simp only [successors,Function.comp_apply] <;> aesop

private theorem step_next [DecidableEq K] {C : StackCode K Q} {q s q' t} (step : StackStep C q s q' t)
    {good : Q → Prop} (h : successors good (C q)) : good q' := by
  cases step with
  | push eq => simpa only [eq,successors] using h
  | goto eq => simpa only [eq,successors] using h
  | pop eq =>
    rw [eq] at h
    exact h _

variable {p r k a m g : ℕ} {Γ : Type} (P : TeamOpcode.Program p r k a)
variable (lib : Fin a → Macro Q Γ m g)

/-- Once initialization finishes the processor can visit the loop, final frame,
sorter and terminal states. None of these can enter the frame startup again. -/
def afterStartup : Processor.Label P Q m g → Prop
  | .block (.startup _ _) => False
  | .block _ | .close _ _ | .sort _ _ | .reject => True
  | _ => False

private theorem finish_late (sign : Option Bool) (ok : Bool) :
    afterStartup P (.block (Endpoint.finishLabel sign ok) : Processor.Label P Q m g) := by
  cases ok <;> trivial

private theorem phase_step (q : Processor.Label P Q m g) (late : afterStartup P q) :
    successors (afterStartup P) (Processor.code P lib q) := by
  cases q with
  | block x =>
    cases x with
    | startup => contradiction
    | done => trivial
    | invalid => trivial
    | loop last x =>
      rw [Processor.code,successor_rename] <;> try (intro sg eq; cases eq)
      cases x <;> simp only [Endpoint.code] <;> first | trivial | exact all_successors _ _ (fun _ => by trivial) _
    | finish sign x =>
      rw [Processor.code,successor_rename] <;> try (intro sg eq; cases eq)
      cases x <;> simp only [Endpoint.code] <;> first | apply finish_late | exact all_successors _ _ (fun _ => by trivial) _
  | close sign x =>
    change successors _ ((_ : StackOp _ _).rename _ _)
    apply all_successors
    rintro (_|_) <;> trivial
  | sort sign x =>
    apply all_successors
    intro; trivial
  | reject => trivial
  | _ => contradiction

/-- The original processor never returns from an already started RAM loop to the
initial endpoint state. -/
theorem afterStartup_runs {t q s q' s'} (run : StackRuns (Processor.code P lib) t q s q' s')
    (late : afterStartup P q) : afterStartup P q' := by
  induction run with
  | nil => exact late
  | cons step tail ih => exact ih (step_next step (phase_step P lib _ late))

private theorem step_lift_row {K J Q R : Type} [DecidableEq K] [DecidableEq J] {src : StackCode K Q}
    {target : StackCode J R} {q s q' s'} (step : StackStep src q s q' s') (ports : K → J)
    (inj : Function.Injective ports) (label : Q → R) (outer : Stacks J)
    (row : target (label q) = (src q).rename ports label) :
    StackStep target (label q) (installStacks ports outer s) (label q') (installStacks ports outer s') := by
  cases step with
  | push eq =>
    rw [eq,StackOp.rename] at row
    simpa only [installStacks_at inj,installStacks_update inj] using
      (StackStep.push (s := installStacks ports outer s) row)
  | pop eq =>
    rw [eq,StackOp.rename] at row
    simpa only [Function.comp_apply,installStacks_at inj,installStacks_update inj] using
      (StackStep.pop (s := installStacks ports outer s) row)
  | goto eq => exact .goto (row.trans (by simp [eq]))

/-- Transport any actual physical prelude into a processor that changes only the
private-call phase, while retaining the trusted template and all other extra stacks. -/
theorem lift_prelude {R : Type} {J : Type} [DecidableEq J] (target : StackCode J R)
    (ports : Layout.Port r k (m*g) → J) (inj : Function.Injective ports) (label : Processor.Label P Q m g → R)
    (outer : Stacks J) (rows : ∀ q, ¬ afterStartup P q → target (label q) = ((Processor.code P lib) q).rename ports label)
    {t q s q' s'} (run : StackRuns (Processor.code P lib) t q s q' s') (early : ¬ afterStartup P q') :
    StackRuns target t (label q) (installStacks ports outer s) (label q') (installStacks ports outer s') := by
  induction run with
  | nil => exact .nil ..
  | cons step tail ih =>
    have e : ¬ afterStartup P _ := fun h => early (afterStartup_runs P lib (.cons step tail) h)
    exact .cons (step_lift_row step ports inj label outer (rows _ e)) (ih early)

end TeamSite.TrustedClock

end BorderVNP
end Computability
end OAI

import OAI.Computability.VPVNP.RAMTapeISAPrepare
import Mathlib.Data.Fintype.Sigma

/-!
# One finite stack control for a fixed RAM instruction table

The control for a template contains entry and exit states for every program
counter and the finite states of its operand routines. Its states and code
are fixed before choosing a word width, public data, or a private execution.
The typed boundary states allow the caller to implement external accesses,
binary choices, the per-instruction clock and return propagation.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.ISA

open BurstRAM PrivateRAM

variable {v w p r k : ℕ}

/-- Dispatcher states for program-counter entry, execution of its preparation routine,
instruction exit, and typed callback. -/
abbrev State (T : Template p r k) :=
  Fin p ⊕ ((i : Fin p) × (prepare (T.code i)).State) ⊕ Fin p ⊕ Callback p r

/-- Enter the fixed table at the given program counter. -/
def entry (T : Template p r k) (pc : Fin p) : State T := .inl pc

/-- Embed a typed instruction exit in the dispatcher state space. -/
def callback (T : Template p r k) (cb : Callback p r) : State T := .inr (.inr (.inr cb))

private def localState (T : Template p r k) (i : Fin p) (q : (prepare (T.code i)).State) : State T :=
  .inr (.inl ⟨i, q⟩)

private def finishState (T : Template p r k) (i : Fin p) : State T := .inr (.inr (.inl i))

/-- Identify precisely the outer-controller callback boundaries. -/
def resume? (T : Template p r k) : State T → Option (Callback p r)
  | .inr (.inr (.inr cb)) => some cb
  | _ => none

@[simp] theorem resume_callback (T : Template p r k) (cb : Callback p r) :
    resume? T (callback T cb) = some cb := rfl

@[simp] theorem resume_entry (T : Template p r k) (i : Fin p) : resume? T (entry T i) = none := rfl

private def finishOp (T : Template p r k) (i : Instr v p r k) : StackOp (Port r k) (State T) :=
  match i with
  | .jumpEq .. | .jumpLt .. => .pop (.work 0) fun flag => callback T (exitFor i (flag.getD false))
  | _ => .goto (callback T (exitFor i false))

/-- The complete deterministic dispatch table, with callbacks initially
represented by halts. Linking replaces their behavior in the caller. -/
def code (T : Template p r k) : StackCode (Port r k) (State T)
  | .inl i => .goto (localState T i (prepare (T.code i)).body.entry)
  | .inr (.inl ⟨i, q⟩) => ((prepare (T.code i)).body.code q).rename id
      (fun next => next.elim (finishState T i) (localState T i))
  | .inr (.inr (.inl i)) => finishOp T (T.code i)
  | .inr (.inr (.inr _)) => .halt true

theorem resume_none_of_continuing (T : Template p r k) (q : State T) (h : (code T q).returns = false) :
    resume? T q = none := by
  rcases q with i | q | i | cb <;> first | rfl | contradiction

private theorem prepare_link (T : Template p r k) (i : Fin p) {t : ℕ} {s out : Stacks (Port r k)}
    (h : (prepare (T.code i)).Runs t s out) :
    StackRuns (code T) t (localState T i (prepare (T.code i)).body.entry) s (finishState T i) out := by
  let routine := prepare (T.code i)
  let labels (q : Option routine.State) : State T := q.elim (finishState T i) (localState T i)
  have hc (q : Option routine.State) (hn : (routine.body.standalone q).returns = false) :
      code T (labels q) = (routine.body.standalone q).rename id labels := by
    cases q with
    | none => contradiction
    | some q => rfl
  have hi (t : Stacks (Port r k)) : installStacks id s t = t := by
    funext j
    exact installStacks_at Function.injective_id s t j
  simpa only [labels, Option.elim_none, Option.elim_some, hi] using
    h.lift id Function.injective_id labels s hc

private theorem finish_step (T : Template p r k) (pc : Fin p) (pub : Fin k → Word w) (c : LogConfig w p r) :
    let i := T.code pc
    StackStep (code T) (finishState T pc) (preparedBank i pub c)
      (callback T (exitFor i ((jumpTest i c).getD false))) (configBank pub (post i pub c)) := by
  dsimp only
  cases h : T.code pc <;> try exact .goto (by simp [code, finishState, h, finishOp, jumpTest])
  all_goals
    let s := configBank pub c
    let b := (jumpTest (T.code pc) c).getD false
    have hs : s (.work 0) = [] := rfl
    have he : code T (finishState T pc) = .pop (.work 0)
        (fun flag => callback T (exitFor (T.code pc) (flag.getD false))) := by
      simp only [code, finishState, h, finishOp]
    have hh := StackStep.pop (s := Function.update s (.work 0) [b]) he
    have hu : Function.update s (.work 0) [] = s := by rw [← hs, Function.update_eq_self]
    simp only [Function.update_self, List.head?_cons, Option.getD_some, List.tail_cons,
      Function.update_idem, hu] at hh
    simpa only [s, b, h, preparedBank, post, jumpTest, Option.getD_some] using hh

/-- The outgoing bank and the typed callback are explicitly determined by the
instruction, independently of how the caller uses either one. -/
theorem dispatch_step (T : Template p r k) (pub : Fin k → Word w) (c : LogConfig w p r) :
    let i := T.code c.pc
    ∃ steps ≤ prepareBound w c.writes.length + 2,
      StackRuns (code T) steps (entry T c.pc) (configBank pub c)
        (callback T (exitFor i ((jumpTest i c).getD false))) (configBank pub (post i pub c)) := by
  dsimp only
  let i := T.code c.pc
  obtain ⟨t, ht, hprep⟩ := prepare_runs i pub c
  have hb : StackStep (code T) (entry T c.pc) (configBank pub c)
      (localState T c.pc (prepare i).body.entry) (configBank pub c) := .goto rfl
  have he := finish_step T c.pc pub c
  exact ⟨(t+1)+1, by omega, .cons hb ((prepare_link T c.pc hprep).trans (.cons he (.nil ..)))⟩

/-- Every reached instruction follows its fixed template table to a typed exit
and implements exactly one native small step. The pathwise cost includes the
initial transfer and the final callback selection. -/
theorem dispatch_run (T : Template p r k) (pub : Fin k → Word w) (c : LogConfig w p r) :
    ∃ steps cb postCfg, steps ≤ prepareBound w c.writes.length + 2 ∧
      StackRuns (code T) steps (entry T c.pc) (configBank pub c) (callback T cb) (configBank pub postCfg) ∧
      cb.action postCfg = (T.instantiate w pub).logProgram.step c := by
  obtain ⟨t, ht, hrun⟩ := dispatch_step T pub c
  exact ⟨t, _, _, ht, hrun, callback_action (T.code c.pc) pub c⟩

end RAMTape.ISA

end VPVNP
end Computability
end OAI

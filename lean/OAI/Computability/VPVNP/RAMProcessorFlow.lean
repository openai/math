import OAI.Computability.VPVNP.RAMTapeISAPorts

/-!
# Linking burst-processor stages with named exits

The call interpreter must return to one of several program counters, request
an external read or write, or finish its call. A fragment's local rows can
name both local continuations and arbitrary exits. Linking selects the entry
of the destination immediately, with no added step on these transfers.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape

/-- A finite stack-code block whose instructions can continue at a local state or transfer to a
named exit. -/
structure Fragment (K L : Type) where
  /-- Finite set of instruction states internal to this fragment. -/
  State : Type
  [finiteState : Fintype State]
  /-- Initial local instruction state on entry to the fragment. -/
  entry : State
  /-- Instruction at each local state, with successors selected from local states and named
  exits. -/
  code : State → StackOp K (State ⊕ L)

attribute [instance] Fragment.finiteState

namespace Fragment

variable {K L Q : Type}

/-- Standalone fragment table that executes the local code and treats every named exit as an
accepting halt. -/
def isolated (f : Fragment K L) : StackCode K (f.State ⊕ L)
  | .inl q => f.code q
  | .inr _ => .halt true

/-- An execution from fragment entry to the specified named exit in exactly the stated number
of steps and with the stated final stacks. -/
abbrev Runs [DecidableEq K] (f : Fragment K L) (t : ℕ) (s : Stacks K) (exit : L) (out : Stacks K) :=
  StackRuns f.isolated t (.inl f.entry) s (.inr exit) out

/-- Form a one-instruction fragment whose continuations are all named exits. -/
def direct (op : StackOp K L) : Fragment K L :=
  ⟨Unit, (), fun _ => op.rename id Sum.inr⟩

/-- Turn a finite routine into a fragment that transfers a normal return to the specified exit
label. -/
def returning (r : FiniteRoutine K) (next : L) : Fragment K L :=
  ⟨r.State, r.body.entry, fun q => (r.body.code q).rename id (Option.elim · (.inr next) Sum.inl)⟩

/-- The continuation after an ordinary subroutine can be any flow label. -/
theorem returning_runs [DecidableEq K] {r : FiniteRoutine K} {t s u}
    (h : r.Runs t s u) (next : L) : (returning r next).Runs t s next u := by
  let labels : Option r.State → (returning r next).State ⊕ L := fun q => q.elim (.inr next) Sum.inl
  have same (s t : Stacks K) : installStacks id s t = t := by
    funext i
    exact installStacks_at Function.injective_id s t i
  have link := h.lift id Function.injective_id labels s
    (target := (returning r next).isolated) (by
      intro q hq
      cases q with
      | none => contradiction
      | some q => rfl)
  change StackRuns (returning r next).isolated t (.inl r.body.entry) s (.inr next) u
  change StackRuns (returning r next).isolated t (.inl r.body.entry) (installStacks id s s) (.inr next) (installStacks id s u) at link
  simpa only [same] using link

/-- Install a multi-exit program. A designated boundary row is intercepted
on entry, allowing the caller to decide what follows each returned action. -/
def fromCode [Fintype Q] (src : StackCode K Q) (entry : Q) (exits : Q → Option L) :
    Fragment K L :=
  ⟨Q, entry, fun q => match exits q with
    | some l => .goto (.inr l)
    | none => (src q).rename id (fun r => (exits r).elim (.inl r) Sum.inr)⟩

theorem fromCode_runs [DecidableEq K] [Fintype Q] {src : StackCode K Q} {entry finish : Q}
    (exits : Q → Option L) (he : exits entry = none) {next : L} (hx : exits finish = some next)
    (hb : ∀ q, (src q).returns = false → exits q = none) {t s u}
    (run : StackRuns src t entry s finish u) :
    (fromCode src entry exits).Runs t s next u := by
  let labels : Q → (fromCode src entry exits).State ⊕ L :=
    fun q => (exits q).elim (.inl q) Sum.inr
  have same (s t : Stacks K) : installStacks id s t = t := by
    funext i
    exact installStacks_at Function.injective_id s t i
  have link := run.lift id Function.injective_id labels s
    (target := (fromCode src entry exits).isolated) (by
      intro q hq
      simp only [labels, hb q hq, Option.elim_none, isolated, fromCode])
  change StackRuns (fromCode src entry exits).isolated t (.inl entry) s (.inr next) u
  simpa only [labels, he, hx, Option.elim_none, Option.elim_some, same] using link

/-- Place a fragment's ports inside a larger bank, leaving the remaining
stacks available to the caller. -/
def onPorts {J : Type} (f : Fragment K L) (ports : K → J) : Fragment J L :=
  ⟨f.State, f.entry, fun q => (f.code q).rename ports id⟩

theorem runs_onPorts {J : Type} [DecidableEq K] [DecidableEq J] {f : Fragment K L}
    (ports : K → J) (hi : Function.Injective ports) (base : Stacks J)
    {t s exit u} (run : f.Runs t s exit u) :
    (f.onPorts ports).Runs t (installStacks ports base s) exit (installStacks ports base u) := by
  have h := run.lift ports hi id base (target := (f.onPorts ports).isolated) (by
    intro q hq
    cases q with
    | inl _ => rfl
    | inr _ => contradiction)
  exact h

end Fragment

namespace ProcessorFlow

variable {K L : Type}

/-- Instruction address in the linked processor, pairing a block label with a local state of
that block. -/
abbrev State (blocks : L → Fragment K L) := Σ l, (blocks l).State

/-- Select a named block and its entry state as the linked instruction address. -/
def enter (blocks : L → Fragment K L) (l : L) : State blocks := ⟨l, (blocks l).entry⟩

/-- Resolve a successor by continuing inside the current block or entering the destination
named by an exit. -/
def next (blocks : L → Fragment K L) (l : L) : (blocks l).State ⊕ L → State blocks :=
  Sum.elim (fun q => ⟨l, q⟩) (enter blocks)

/-- Link the fragment tables into one stack program by resolving each local successor and each
named transfer. -/
def program (blocks : L → Fragment K L) : StackCode K (State blocks) :=
  fun ⟨l, q⟩ => ((blocks l).code q).rename id (next blocks l)

/-- A whole deterministic path in a fragment runs unchanged in the linked
program, arriving directly at the entry of its exit label. -/
theorem run [DecidableEq K] {blocks : L → Fragment K L} {l exit t s u}
    (h : (blocks l).Runs t s exit u) : StackRuns (program blocks) t (enter blocks l) s (enter blocks exit) u := by
  have same (s t : Stacks K) : installStacks id s t = t := by
    funext i
    exact installStacks_at Function.injective_id s t i
  have link := h.lift id Function.injective_id (next blocks l) s (target := program blocks) (by
    intro q hq
    cases q with
    | inl q => rfl
    | inr r => contradiction)
  simpa only [enter, next, Sum.elim_inl, Sum.elim_inr, same] using link

end ProcessorFlow
end RAMTape

end VPVNP
end Computability
end OAI

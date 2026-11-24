import OAI.Computability.VPVNP.RAMTapeStackLift

/-!
# Structured finite-control programs for bit stacks

The local validator in §10 performs nested scans, branches and calls. Each routine
has one normal return and may also halt with acceptance or rejection. Linking a
return to the next instruction introduces no extra machine step. All constructions
on finite controls use only finite sums and individual new labels.

The continuation semantics counts accepting paths with a fixed remaining step budget.
It permits exact accounting through a call even when the callee makes binary choices.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape

/-- A control label is local to this routine. `none` in an instruction's continuation
returns to the caller, while a halt ends the entire execution. -/
structure Routine (K Q : Type*) where
  /-- The local control label at which an invocation of the routine begins. -/
  entry : Q
  /-- The stack instruction at each local control label, using an absent successor to return to
  the caller. -/
  code : Q → StackOp K (Option Q)

namespace Routine

variable {K Q R M : Type*}

/-- Closed executable with an arbitrary halt outcome at the normal-return boundary. -/
def close (r : Routine K Q) (outcome : Bool) : StackCode K (Option Q)
  | none => .halt outcome
  | some q => r.code q

/-- Closes a routine as a stack program by installing a rejecting halt at its normal-return
boundary. -/
abbrev standalone (r : Routine K Q) := r.close false

/-- A deterministic execution from the routine entry to normal return in exactly the indicated
number of instructions, with the specified initial and final stack banks. -/
abbrev Runs [DecidableEq K] (r : Routine K Q) (t : ℕ) (s out : Stacks K) :=
  StackRuns r.standalone t (some r.entry) s none out

/-- Install a routine's control into its caller, redirecting normal returns. -/
def install (r : Routine K Q) (label : Q → R) (resume : Option R) (q : Q) :
    StackOp K (Option R) :=
  (r.code q).rename id (Option.elim · resume (some ∘ label))

/-- Returns normally in one instruction, preserving the stack bank. -/
def ret : Routine K Unit := ⟨(), fun _ => .goto none⟩

/-- Pushes one bit onto the specified stack and returns normally. -/
def push (k : K) (b : Bool) : Routine K Unit := ⟨(), fun _ => .push k b none⟩

/-- Halts the whole execution with the specified acceptance bit. -/
def halt (accept : Bool) : Routine K Unit := ⟨(), fun _ => .halt accept⟩

/-- Run both routines, returning normally only when the second does. -/
def followedBy (a : Routine K Q) (b : Routine K R) : Routine K (Q ⊕ R) :=
  ⟨.inl a.entry, Sum.elim (a.install Sum.inl (some (.inr b.entry))) (b.install Sum.inr none)⟩

/-- Two branch slots count separately, even for routines with identical effects. -/
def choose (a : Routine K Q) (b : Routine K R) : Routine K (Unit ⊕ (Q ⊕ R)) where
  entry := .inl ()
  code
    | .inl _ => .choose (some (.inr (.inl a.entry))) (some (.inr (.inr b.entry)))
    | .inr (.inl q) => a.install (Sum.inr ∘ Sum.inl) none q
    | .inr (.inr q) => b.install (Sum.inr ∘ Sum.inr) none q

/-- Pop one bit, dispatching separately on an empty stack, zero, and one. -/
def popCase (k : K) (missing : Routine K M) (low : Routine K Q) (high : Routine K R) :
    Routine K (Unit ⊕ (M ⊕ (Q ⊕ R))) where
  entry := .inl ()
  code
    | .inl _ => .pop k fun
        | none => some (.inr (.inl missing.entry))
        | some false => some (.inr (.inr (.inl low.entry)))
        | some true => some (.inr (.inr (.inr high.entry)))
    | .inr (.inl q) => missing.install (Sum.inr ∘ Sum.inl) none q
    | .inr (.inr (.inl q)) => low.install (Sum.inr ∘ Sum.inr ∘ Sum.inl) none q
    | .inr (.inr (.inr q)) => high.install (Sum.inr ∘ Sum.inr ∘ Sum.inr) none q

/-- An empty stack ends the loop. On a present bit, first run the selected body.
When it returns, `repeatOn` decides whether to continue or to finish the scan. -/
def popLoop (k : K) (repeatOn : Bool → Bool) (low : Routine K Q) (high : Routine K R) :
    Routine K (Unit ⊕ (Q ⊕ R)) where
  entry := .inl ()
  code
    | .inl _ => .pop k fun
        | none => none
        | some false => some (.inr (.inl low.entry))
        | some true => some (.inr (.inr high.entry))
    | .inr (.inl q) => low.install (Sum.inr ∘ Sum.inl) (if repeatOn false then some (.inl ()) else none) q
    | .inr (.inr q) => high.install (Sum.inr ∘ Sum.inr) (if repeatOn true then some (.inl ()) else none) q

variable [DecidableEq K]

/-- At a normal return the continuation receives the exact remaining fuel and stacks. -/
def countFrom (r : Routine K Q) (continuation : ℕ → Stacks K → ℕ) :
    ℕ → Option Q → Stacks K → ℕ
  | t, none, s => continuation t s
  | 0, some _, _ => 0
  | t + 1, some q, s =>
    match r.code q with
    | .push k b next => r.countFrom continuation t next (Function.update s k (b :: s k))
    | .pop k next => r.countFrom continuation t (next (s k).head?) (Function.update s k (s k).tail)
    | .goto next => r.countFrom continuation t next s
    | .choose a b => r.countFrom continuation t a s + r.countFrom continuation t b s
    | .halt accept => accept.toNat

/-- Counts accepting branches from the routine entry within the fuel budget, using the
continuation’s count at each normal return. -/
abbrev count (r : Routine K Q) (continuation : ℕ → Stacks K → ℕ) (t : ℕ) (s : Stacks K) :=
  r.countFrom continuation t (some r.entry) s

/-- A fixed closed machine realizes the continuation semantics for either return outcome. -/
theorem stackPaths_close (r : Routine K Q) (b : Bool) (t : ℕ) (q : Option Q) (s : Stacks K) :
    stackPaths (r.close b) t q s = r.countFrom (fun n _ => if n = 0 then 0 else b.toNat) t q s := by
  induction t generalizing q s with
  | zero => cases q <;> rfl
  | succ t ih =>
    cases q with
    | none => rfl
    | some q =>
      simp only [stackPaths, close, countFrom]
      cases r.code q <;> simp only [ih]

/-- An installed control counts precisely the same paths as its original routine,
then resumes with the residual budget. -/
theorem countFrom_install (outer : Routine K R) (inner : Routine K Q)
    (label : Q → R) (resume : Option R)
    (h : ∀ q, outer.code (label q) = inner.install label resume q)
    (continuation : ℕ → Stacks K → ℕ) (t : ℕ) (q : Option Q) (s : Stacks K) :
    outer.countFrom continuation t (q.elim resume (some ∘ label)) s =
      inner.countFrom (fun n st => outer.countFrom continuation n resume st) t q s := by
  induction t generalizing q s with
  | zero => cases q <;> rfl
  | succ t ih =>
    cases q with
    | none => rfl
    | some q =>
      simp only [Option.elim_some, Function.comp_apply, countFrom, h, install]
      cases inner.code q <;> simp only [StackOp.rename, Function.comp_apply, id_eq, ih]

@[simp] theorem countFrom_none (r : Routine K Q) (c : ℕ → Stacks K → ℕ) (t : ℕ) (s : Stacks K) :
    r.countFrom c t none s = c t s := by cases t <;> rfl

/-- Sequencing spends no instruction on transferring control from one routine to the next. -/
theorem count_followedBy (a : Routine K Q) (b : Routine K R)
    (c : ℕ → Stacks K → ℕ) (t : ℕ) (s : Stacks K) :
    (a.followedBy b).count c t s = a.count (b.count c) t s := by
  have second (n : ℕ) (st : Stacks K) :
      (a.followedBy b).countFrom c n (some (.inr b.entry)) st = b.count c n st := by
    simpa only [Option.elim_some, Function.comp_apply, countFrom_none] using
      countFrom_install (a.followedBy b) b Sum.inr none (fun _ => rfl) c n (some b.entry) st
  change (a.followedBy b).countFrom c t (some (.inl a.entry)) s =
    a.countFrom (fun n st => b.count c n st) t (some a.entry) s
  simpa only [Option.elim_some, Function.comp_apply, second] using
    countFrom_install (a.followedBy b) a Sum.inl (some (.inr b.entry)) (fun _ => rfl)
      c t (some a.entry) s

private theorem installed_normal (outer : Routine K R) (inner : Routine K Q)
    (label : Q → R) (h : ∀ q, outer.code (label q) = inner.install label none q)
    (c : ℕ → Stacks K → ℕ) (n : ℕ) (s : Stacks K) :
    outer.countFrom c n (some (label inner.entry)) s = inner.count c n s := by
  simpa only [Option.elim_some, Function.comp_apply, countFrom_none] using
    countFrom_install outer inner label none h c n (some inner.entry) s

/-- A binary nondeterministic instruction contributes both of its branch counts. -/
theorem count_choose (a : Routine K Q) (b : Routine K R)
    (c : ℕ → Stacks K → ℕ) (t : ℕ) (s : Stacks K) :
    (choose a b).count c (t + 1) s = a.count c t s + b.count c t s := by
  change (choose a b).countFrom c t (some (.inr (.inl a.entry))) s +
    (choose a b).countFrom c t (some (.inr (.inr b.entry))) s = _
  exact congrArg₂ (· + ·)
    (installed_normal (choose a b) a (Sum.inr ∘ Sum.inl) (fun _ => rfl) c t s)
    (installed_normal (choose a b) b (Sum.inr ∘ Sum.inr) (fun _ => rfl) c t s)

/-- A case instruction consumes exactly one machine step and removes the head when present. -/
theorem count_popCase (k : K) (missing : Routine K M) (low : Routine K Q) (high : Routine K R)
    (c : ℕ → Stacks K → ℕ) (t : ℕ) (s : Stacks K) :
    (popCase k missing low high).count c (t + 1) s =
      let st := Function.update s k (s k).tail
      match (s k).head? with
      | none => missing.count c t st
      | some false => low.count c t st
      | some true => high.count c t st := by
  let outer := popCase k missing low high
  unfold count
  rw [countFrom]
  cases hb : (s k).head? with
  | none =>
    simpa only [outer, popCase, hb, Function.comp_apply, count] using installed_normal outer missing (Sum.inr ∘ Sum.inl)
      (fun _ => rfl) c t (Function.update s k (s k).tail)
  | some b =>
    cases b
    · simpa only [outer, popCase, hb, Function.comp_apply, count] using installed_normal outer low (Sum.inr ∘ Sum.inr ∘ Sum.inl)
        (fun _ => rfl) c t (Function.update s k (s k).tail)
    · simpa only [outer, popCase, hb, Function.comp_apply, count] using installed_normal outer high (Sum.inr ∘ Sum.inr ∘ Sum.inr)
        (fun _ => rfl) c t (Function.update s k (s k).tail)

/-- One test of the loop selects the body and links its normal return either to the next test
or to the caller. The body may make any number of binary choices before returning. -/
theorem count_popLoop (k : K) (repeatOn : Bool → Bool) (low : Routine K Q) (high : Routine K R)
    (c : ℕ → Stacks K → ℕ) (t : ℕ) (s : Stacks K) :
    (popLoop k repeatOn low high).count c (t + 1) s =
      let st := Function.update s k (s k).tail
      let resume (b : Bool) := if repeatOn b then (popLoop k repeatOn low high).count c else c
      match (s k).head? with
      | none => c t st
      | some false => low.count (resume false) t st
      | some true => high.count (resume true) t st := by
  let outer := popLoop k repeatOn low high
  have branch (b : Bool) :
      (fun n st => outer.countFrom c n (if repeatOn b then some (.inl ()) else none) st) =
        (if repeatOn b then outer.count c else c) := by
    cases repeatOn b <;> simp only [Bool.false_eq_true, ite_false, ite_true, countFrom_none]
    rfl
  unfold count
  rw [countFrom]
  cases hb : (s k).head? with
  | none => simp only [popLoop, hb, countFrom_none]
  | some b =>
    cases b
    · have h := countFrom_install outer low (Sum.inr ∘ Sum.inl)
        (if repeatOn false then some (.inl ()) else none) (fun _ => rfl)
        c t (some low.entry) (Function.update s k (s k).tail)
      rw [branch] at h
      simpa only [outer, popLoop, hb, Option.elim_some, Function.comp_apply, count] using h
    · have h := countFrom_install outer high (Sum.inr ∘ Sum.inr)
        (if repeatOn true then some (.inl ()) else none) (fun _ => rfl)
        c t (some high.entry) (Function.update s k (s k).tail)
      rw [branch] at h
      simpa only [outer, popLoop, hb, Option.elim_some, Function.comp_apply, count] using h

end Routine
end RAMTape

end VPVNP
end Computability
end OAI

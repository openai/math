import Mathlib.Tactic

/-! A first-order, resumable control stack for the two groups of recursive trial calls.
Parameters describe the numeric packets handled by each phase. The stack contains only
data packets, counters, and finite lists, including after a designated query. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Trial

universe u
variable {I P R C Q : Type u}

/-- Fixed phase operations. `finish` replays the current feedback scan on its local
chronological replies and either supplies one completed call or requests its next label. -/
structure Kernel (I P R C Q : Type u) where
  leaf : I → R
  prepare : I → List C → P
  childInput : I → P → I
  assemble : I → List C → R
  finish : I → List C → P → R → List Bool → C ⊕ Q

/-- Saved parent call, independent of the child output and any future oracle label. -/
structure Frame (I P C : Type u) where
  childFuel : ℕ
  remaining : ℕ
  input : I
  «prefix» : List C
  prepared : P

/-- The concrete program counter. `feedback` keeps only data from the current scan. -/
inductive PC (I P R C : Type u)
  | enter (fuel : ℕ) (input : I)
  | schedule (childFuel remaining : ℕ) (input : I) (rows : List C)
  | returned (out : R)
  | feedback (saved : Frame I P C) (out : R) (localReplies : List Bool)

structure State (I P R C : Type u) where
  pc : PC I P R C
  stack : List (Frame I P C)

/-- Both continuations of a query are ordinary data states. -/
inductive Action (I P R C Q : Type u)
  | proceed (state : State I P R C)
  | ask (query : Q) (ifFalse ifTrue : State I P R C)
  | halt (out : R)

def initial (fuel : ℕ) (input : I) : State I P R C := ⟨.enter fuel input, []⟩

/-- Execute one control instruction of the depth-first recursive schedule. -/
def step (ops : Kernel I P R C Q) (calls : ℕ) (state : State I P R C) : Action I P R C Q :=
  match state.pc with
  | .enter 0 input => .proceed ⟨.returned (ops.leaf input), state.stack⟩
  | .enter (fuel+1) input => .proceed ⟨.schedule fuel calls input [], state.stack⟩
  | .schedule _ 0 input xs => .proceed ⟨.returned (ops.assemble input xs), state.stack⟩
  | .schedule fuel (rem+1) input xs =>
    let start := ops.prepare input xs
    let frame : Frame I P C := ⟨fuel, rem, input, xs, start⟩
    .proceed ⟨.enter fuel (ops.childInput input start), frame :: state.stack⟩
  | .returned out =>
    match state.stack with
    | [] => .halt out
    | f :: ss => .proceed ⟨.feedback f out [], ss⟩
  | .feedback f out tape =>
    match ops.finish f.input f.prefix f.prepared out tape with
    | .inl c => .proceed ⟨.schedule f.childFuel f.remaining f.input (f.prefix ++ [c]), state.stack⟩
    | .inr q => .ask q ⟨.feedback f out (tape ++ [false]), state.stack⟩
        ⟨.feedback f out (tape ++ [true]), state.stack⟩

/-- Actual finite small-step runs, counting every nonhalting control instruction.
The labels in the trace are chosen freely. -/
inductive Steps (ops : Kernel I P R C Q) (calls : ℕ) :
    State I P R C → List (Q × Bool) → ℕ → State I P R C → Prop where
  | refl (s) : Steps ops calls s [] 0 s
  | silent {s t u tr n} (h : step ops calls s = .proceed t) (rest : Steps ops calls t tr n u) :
      Steps ops calls s tr (n+1) u
  | answer {s f t u tr n q} (reply : Bool) (h : step ops calls s = .ask q f t)
      (rest : Steps ops calls (if reply then t else f) tr n u) :
      Steps ops calls s ((q,reply) :: tr) (n+1) u

theorem Steps.trans {ops : Kernel I P R C Q} {calls : ℕ} {s t u : State I P R C}
    {tr tr' n n'} (a : Steps ops calls s tr n t) (b : Steps ops calls t tr' n' u) :
    Steps ops calls s (tr++tr') (n+n') u := by
  induction a with
  | refl => simpa
  | silent hs _ ih => simpa only [Nat.succ_add] using Steps.silent hs (ih b)
  | answer reply hs _ ih => simpa only [Nat.succ_add, List.cons_append] using Steps.answer reply hs (ih b)

/-- The transcript yielded by one prefix interpreter, including all free answers. -/
inductive Scan (run : List Bool → C ⊕ Q) : List Bool → List (Q × Bool) → C → Prop where
  | done {t c} (hc : run t = .inl c) : Scan run t [] c
  | ask {t q tr c} (a : Bool) (hq : run t = .inr q) (tail : Scan run (t++[a]) tr c) :
      Scan run t ((q,a) :: tr) c

theorem Scan.steps {ops : Kernel I P R C Q} (calls : ℕ) (f : Frame I P C) (out : R)
    (stack : List (Frame I P C)) {t tr c}
    (scan : Scan (ops.finish f.input f.prefix f.prepared out) t tr c) :
    Steps ops calls ⟨.feedback f out t, stack⟩ tr (tr.length+1)
      ⟨.schedule f.childFuel f.remaining f.input (f.prefix++[c]), stack⟩ := by
  induction scan with
  | done hc =>
    exact .silent (by simp [step,hc]) (.refl _)
  | @ask t q tr c a hq hs ih =>
    have hstep : step ops calls ⟨.feedback f out t, stack⟩ = .ask q
        ⟨.feedback f out (t++[false]), stack⟩ ⟨.feedback f out (t++[true]),stack⟩ := by
      simp [step,hq]
    cases a <;> exact .answer _ hstep ih

/-- Reference structured control for one node or an uncompleted prefix of its schedule. -/
inductive Work (I C : Type u)
  | node (fuel : ℕ) (input : I)
  | rounds (childFuel remaining : ℕ) (input : I) (rows : List C)

def Work.pc : Work I C → PC I P R C
  | .node k i => .enter k i
  | .rounds k t i xs => .schedule k t i xs

/-- Big-step semantics of a structural recursive call. It first completes the child,
then obtains its feedback, then advances the prefix of the parent's schedule. -/
inductive Evaluates (ops : Kernel I P R C Q) (calls : ℕ) :
    Work I C → List (Q × Bool) → R → Prop where
  | leaf (i) : Evaluates ops calls (.node 0 i) [] (ops.leaf i)
  | node {k i tr out} (scheduled : Evaluates ops calls (.rounds k calls i []) tr out) :
      Evaluates ops calls (.node (k+1) i) tr out
  | done (k i xs) : Evaluates ops calls (.rounds k 0 i xs) [] (ops.assemble i xs)
  | call {k rem i xs left middle right out row result}
      (child : Evaluates ops calls (.node k (ops.childInput i (ops.prepare i xs))) left out)
      (feedback : Scan (ops.finish i xs (ops.prepare i xs) out) [] middle row)
      (rest : Evaluates ops calls (.rounds k rem i (xs++[row])) right result) :
      Evaluates ops calls (.rounds k (rem+1) i xs) (left ++ middle ++ right) result

/-- Exact overhead outside the individual designated-query replies. -/
def nodeTicks (calls : ℕ) : ℕ → ℕ
  | 0 => 1
  | k+1 => 2 + calls * (nodeTicks calls k + 3)

def Work.ticks (calls : ℕ) : Work I C → ℕ
  | .node k _ => nodeTicks calls k
  | .rounds k r _ _ => 1 + r * (nodeTicks calls k + 3)

/-- Each call's complete transcript is preserved by its first-order stack execution.
The saved outer stack is arbitrary, so the same lemma applies at every nesting depth. -/
theorem Evaluates.steps {ops : Kernel I P R C Q} {calls : ℕ} {w : Work I C} {tr out}
    (eval : Evaluates ops calls w tr out) (stack : List (Frame I P C)) :
    Steps ops calls ⟨w.pc, stack⟩ tr (w.ticks calls + tr.length) ⟨.returned out, stack⟩ := by
  induction eval generalizing stack with
  | leaf i => exact .silent rfl (.refl _)
  | done k i xs =>
    have hs : step ops calls ⟨.schedule k 0 i xs, stack⟩ = .proceed ⟨.returned (ops.assemble i xs),stack⟩ := rfl
    simpa only [Work.pc, Work.ticks, Nat.zero_mul, Nat.add_zero, List.length_nil] using Steps.silent hs (.refl _)
  | @node k i tr out scheduled ih =>
    have total := Steps.silent (show step ops calls ⟨.enter (k+1) i, stack⟩ =
        .proceed ⟨.schedule k calls i [], stack⟩ from rfl) (ih stack)
    convert total using 1
    all_goals simp only [Work.pc, Work.ticks, nodeTicks]
    all_goals omega
  | @call k rem i xs left middle right out row result child feedback rest ihChild ihRest =>
    let f : Frame I P C := ⟨k, rem, i, xs, ops.prepare i xs⟩
    have hs := feedback.steps (ops := ops) calls f out stack
    have ret := Steps.silent (show step ops calls ⟨.returned out, f::stack⟩ =
        .proceed ⟨.feedback f out [], stack⟩ from rfl) hs
    have seq := ((ihChild (f::stack)).trans ret).trans (ihRest stack)
    have start := Steps.silent (show step ops calls ⟨.schedule k (rem+1) i xs, stack⟩ =
        .proceed ⟨.enter k (ops.childInput i (ops.prepare i xs)), f::stack⟩ from rfl) seq
    convert start using 1
    all_goals simp only [Work.pc, Work.ticks, List.length_append, Nat.add_mul, Nat.one_mul]
    all_goals omega

theorem Evaluates.halts {ops : Kernel I P R C Q} {calls fuel : ℕ} {i : I} {tr out}
    (e : Evaluates ops calls (.node fuel i) tr out) :
    ∃ stop, Steps ops calls (initial fuel i) tr (nodeTicks calls fuel + tr.length) stop ∧
      step ops calls stop = .halt out :=
  ⟨⟨.returned out, []⟩, e.steps [], rfl⟩

end Trial
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI

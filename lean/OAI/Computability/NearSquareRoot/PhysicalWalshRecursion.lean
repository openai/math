import OAI.Computability.NearSquareRoot.PhysicalWalshOpen
import OAI.Computability.NearSquareRoot.PhysicalWalshRelease

/-! # Closing a finite Walsh program under a recursive call

Each recursive request consists of one tag followed by its serialized bank. The
fixed program reads the tag, executes the base or template command, and returns
to the caller. The environment supplied to the template certifies actual jumps
to this same program on strictly smaller widths. The template may issue any
fixed number of calls on data computed by earlier calls.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh

open IntegerMultiplication Code Space

/-- An invocation `x` includes its row contents. Its world determines the
resource bounds, recursion level and permissible child layouts. -/
structure RecSpec (X U : Type*) where
  world : X → U
  level : U → ℕ
  payload : X → Tree
  reply : X → Tree
  child : U → U → Prop
  decreases : ∀ {u v}, child u v → level v < level u
  scan : U → ℕ
  arena : U → ℕ
  arena_le : ∀ u, arena u ≤ scan u

namespace RecSpec
variable {X U : Type*} (d : RecSpec X U)

/-- Input bank of a terminal two-bit transform. -/
abbrev Base := {x : X // d.level (d.world x) = 0}

/-- Input bank of a recursive template. -/
abbrev Step := {x : X // 0 < d.level (d.world x)}

/-- The tag lies at the top of the stack, outside the bank payload. -/
def query (x : X) : Tree := .fork (.atom (decide (0 < d.level (d.world x)))) (d.payload x)

/-- Availability of the recursive entry point at the head of the lexical environment. -/
def meter : Meter U where
  scan := d.scan
  arena := d.arena
  arena_le := d.arena_le
  permit env u t s := ∀ y, d.child u (d.world y) → ∀ p b, DeckCap b p →
    BoundedFits env (.again 0) (pile 0 (d.query y) p) (pile 0 (d.reply y) p) t (b+s) s

/-- Execute the open child call. The clock and peak bounds charge the child
at coefficient one and are independent of the cost of the parent template. -/
theorem call {Y : Type*} (u : Y → U) (y : Y → X) (h : ∀ z, d.child (u z) (d.world (y z))) :
    OpenRun d.meter 1 u (d.query ∘ y) (d.reply ∘ y) := by
  refine ⟨.again 0, 0, fun z env t s permit p b hp => ?_⟩
  simpa using permit (y z) (h z) p b hp

/-- Time counts all children while peak space counts the largest allowed
child. Both budgets can depend on the full layout of the invocation. -/
structure Recurrence (calls C : ℕ) (T S : U → ℕ) where
  childTime : U → ℕ
  childSpace : U → ℕ
  boundsTime : ∀ {u v}, d.child u v → T v ≤ childTime u
  boundsSpace : ∀ {u v}, d.child u v → S v ≤ childSpace u
  baseTime : ∀ u, d.level u = 0 → C * (d.scan u + 1) ≤ T u
  baseSpace : ∀ u, d.level u = 0 → C * (d.arena u + 1) ≤ S u
  stepTime : ∀ u, 0 < d.level u → C * (d.scan u + 1) + calls * childTime u ≤ T u
  stepSpace : ∀ u, 0 < d.level u → C * (d.arena u + 1) + childSpace u ≤ S u

private theorem taggedCap {p : Deck} {cap : ℕ} {x : Tree} (bit : Bool)
    (h : DeckCap cap (pile 0 x p)) : DeckCap (cap+2) (pile 0 (.fork (.atom bit) x) p) := by
  intro j
  have hj := h j
  by_cases e : j = 0
  · subst j
    simp only [letters_here, List.length_append, Tree.spell_length, Tree.count] at *
    omega
  · simp only [pile_far _ _ (Ne.symm e)] at *
    omega

private theorem dispatch {p : Deck} {env : Env} {c e : Cmd} {q r : Tree} {b t s : ℕ} (bit : Bool)
    (h : BoundedFits env (bif bit then e else c) (pile 0 q p) (pile 0 r p) t (b+s) s) :
    BoundedFits env (Space.decodeBit c e) (pile 0 (.fork (.atom bit) q) p) (pile 0 r p)
      (t+8) (b+(s+2)) (s+2) := by
  have h' := h.mono le_rfl (by omega : b+s ≤ b+(s+2)) (by omega : s ≤ s+2)
  obtain ⟨_,_,run⟩ := h
  have hc : DeckCap (b+(s+2)) (pile 0 (.fork (.atom bit) q) p) := by
    simpa only [Nat.add_assoc] using taggedCap bit (show DeckCap (b+s) _ from run.start)
  exact BoundedFits.decodeBit h' hc (by omega)

/-- One fixed tied command works at every level. Its code and local constant
are selected before either resource recurrence is supplied. -/
theorem tieNamed {calls : ℕ} (baseCmd stepCmd : Cmd)
    (one : ClosedRuns baseCmd (fun x : d.Base => d.scan (d.world x.val))
      (fun x => d.arena (d.world x.val)) (fun x => d.payload x.val) (fun x => d.reply x.val))
    (step : Runs stepCmd d.meter calls (fun x : d.Step => d.world x.val)
      (fun x => d.payload x.val) (fun x => d.reply x.val)) :
    ∃ C : ℕ, ∀ T S : U → ℕ, d.Recurrence calls C T S →
      ∀ x env p b, DeckCap b p → BoundedFits env (.tie (Space.decodeBit baseCmd stepCmd)) (pile 0 (d.query x) p) (pile 0 (d.reply x) p)
        (T (d.world x)) (b + S (d.world x)) (S (d.world x)) := by
  obtain ⟨B,runBase⟩ := one
  obtain ⟨D,runStep⟩ := step
  let body := Space.decodeBit baseCmd stepCmd
  let C := B+D+10
  refine ⟨C,fun T S budget x env => ?_⟩
  have pos (v : U) : 1 ≤ T v := by
    by_cases isBase : d.level v = 0
    · have := budget.baseTime v isBase
      dsimp only [C] at this; rw [Nat.add_mul] at this; omega
    · have := budget.stepTime v (by omega)
      dsimp only [C] at this; rw [Nat.add_mul] at this; omega
  have run (x : X) : ∀ p b, DeckCap b p → BoundedFits (body :: env) body
      (pile 0 (d.query x) p) (pile 0 (d.reply x) p)
      (T (d.world x)-1) (b + S (d.world x)) (S (d.world x)) := by
    induction x using (measure (d.level ∘ d.world)).wf.induction with
    | h x ih =>
      intro p b hp
      by_cases isBase : d.level (d.world x) = 0
      · have baseRun := runBase ⟨x,isBase⟩ (body :: env) p b hp
        have branch := dispatch (c := baseCmd) (e := stepCmd) false baseRun
        dsimp only at branch
        have tm := budget.baseTime _ isBase
        have sp := budget.baseSpace _ isBase
        simp only [C, Nat.add_mul] at tm sp
        simpa only [query, isBase, Nat.lt_irrefl, decide_false, body] using
          branch.mono (time' := T (d.world x)-1) (by omega) (cap' := b + S (d.world x)) (by omega)
            (depth' := S (d.world x)) (by omega)
      · have greater : 0 < d.level (d.world x) := by omega
        have perm : d.meter.permit (body :: env) (d.world x) (budget.childTime (d.world x))
            (budget.childSpace (d.world x)) := by
          intro y hy p' b' hp'
          have childRun := ih y (d.decreases hy) p' b' hp'
          have ht := budget.boundsTime hy
          have hs := budget.boundsSpace hy
          have := pos (d.world y)
          exact childRun.again0.mono (by omega) (Nat.add_le_add_left hs _) hs
        have stepRun := runStep ⟨x,greater⟩ (body :: env) _ _ perm p b hp
        have branch := dispatch (c := baseCmd) (e := stepCmd) true stepRun
        have tm := budget.stepTime _ greater
        have sp := budget.stepSpace _ greater
        simp only [C, Nat.add_mul] at tm sp
        simp only [meter] at branch
        simpa only [query, greater, decide_true, body] using
          branch.mono (time' := T (d.world x)-1) (by omega) (cap' := b + S (d.world x)) (by omega)
            (depth' := S (d.world x)) (by omega)
  intro p b hp
  exact ((run x p b hp).tie).mono (by have := pos (d.world x); omega) le_rfl le_rfl

/-- A closed recursive command under the existential task interfaces used by
individual node algorithms. -/
theorem tie {calls : ℕ}
    (one : BoundedTask (fun x : d.Base => d.scan (d.world x.val))
      (fun x => d.arena (d.world x.val)) (fun x => d.payload x.val) (fun x => d.reply x.val))
    (step : OpenRun d.meter calls (fun x : d.Step => d.world x.val)
      (fun x => d.payload x.val) (fun x => d.reply x.val)) :
    ∃ cmd : Cmd, ∃ C : ℕ, ∀ T S : U → ℕ, d.Recurrence calls C T S →
      ∀ x env p b, DeckCap b p → BoundedFits env cmd (pile 0 (d.query x) p) (pile 0 (d.reply x) p)
        (T (d.world x)) (b + S (d.world x)) (S (d.world x)) := by
  obtain ⟨baseCmd,one⟩ := one
  obtain ⟨stepCmd,step⟩ := step
  exact ⟨_,d.tieNamed baseCmd stepCmd one step⟩

/-- A reusable costed stack task on all tagged input banks. -/
theorem bounded {calls : ℕ}
    (one : BoundedTask (fun x : d.Base => d.scan (d.world x.val))
      (fun x => d.arena (d.world x.val)) (fun x => d.payload x.val) (fun x => d.reply x.val))
    (step : OpenRun d.meter calls (fun x : d.Step => d.world x.val)
      (fun x => d.payload x.val) (fun x => d.reply x.val)) :
    ∃ C : ℕ, ∀ T S : U → ℕ, d.Recurrence calls C T S →
      BoundedTask (T ∘ d.world) (S ∘ d.world) d.query d.reply := by
  obtain ⟨cmd,C,h⟩ := d.tie one step
  refine ⟨C,fun T S budget => ⟨cmd,1,fun x env p b hp => ?_⟩⟩
  apply (h T S budget x env p b hp).mono <;> simp

/-- The recursive template on a conventional multitape machine, including
its output copy and a visited-cell bound independent of its running time. -/
theorem physical {calls : ℕ}
    (one : BoundedTask (fun x : d.Base => d.scan (d.world x.val))
      (fun x => d.arena (d.world x.val)) (fun x => d.payload x.val) (fun x => d.reply x.val))
    (step : OpenRun d.meter calls (fun x : d.Step => d.world x.val)
      (fun x => d.payload x.val) (fun x => d.reply x.val)) :
    ∃ C : ℕ, ∀ T S : U → ℕ, d.Recurrence calls C T S →
      TapeTask (T ∘ d.world) (S ∘ d.world) d.query d.reply := by
  obtain ⟨C,h⟩ := d.bounded one step
  exact ⟨C,fun T S hr => (h T S hr).release⟩

/-- An accounting certificate for the compiled command. The certificate is
used only to measure a trace; it is absent from the input alphabet. -/
structure Certificate (calls C : ℕ) where
  time : U → ℕ
  space : U → ℕ
  valid : d.Recurrence calls C time space

/-- Strengthened physical release in which the *same* finite machine works
for all resource certificates at once. Every certificate for `x` loads the
same serialized input and produces the same serialized answer. -/
theorem uniformMachine {calls : ℕ}
    (one : BoundedTask (fun x : d.Base => d.scan (d.world x.val))
      (fun x => d.arena (d.world x.val)) (fun x => d.payload x.val) (fun x => d.reply x.val))
    (step : OpenRun d.meter calls (fun x : d.Step => d.world x.val)
      (fun x => d.payload x.val) (fun x => d.reply x.val)) :
    ∃ C : ℕ, TapeTask (fun z : d.Certificate calls C × X => z.1.time (d.world z.2))
      (fun z => z.1.space (d.world z.2)) (fun z => d.query z.2) (fun z => d.reply z.2) := by
  obtain ⟨cmd,C,h⟩ := d.tie one step
  refine ⟨C,BoundedTask.release ⟨cmd,1,?_⟩⟩
  rintro ⟨cert,x⟩ env p b hp
  exact (h _ _ cert.valid x env p b hp).mono (by simp) (by simp) (by simp)

end RecSpec
end PhysicalWalsh

end NearSquareRoot
end Computability
end OAI

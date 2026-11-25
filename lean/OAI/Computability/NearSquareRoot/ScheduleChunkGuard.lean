import OAI.Computability.NearSquareRoot.ScheduleSchoolRelease
import OAI.Computability.NearSquareRoot.ScheduleSchoolSegments
import OAI.Computability.NearSquareRoot.ScheduleInterpreterTrial

/-!
# Physical fences for digit calls

A stack-machine segment of height at most `H` is released to fixed tapes.
The same local guard is used at every radius: the endpoints are represented
on two tracks. Its space bound at an arbitrary cutoff applies even if the
candidate fails to return or attempts to cross an endpoint.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ChunkGuard

open IntegerMultiplication IntegerMultiplication.TM
open NearSquareRoot.Uniform (tapeTick)
open Uniform.Fence

variable {A Q I : Type} [DecidableEq I] [Fintype I]

/-- This rule has no length or radius parameter. -/
abbrev rule (k : I) (g : SM.Rule A Q I) := guard (SM.complete k g)

def origin (q : Q) (i : I) (s : List A) : Config (Option A) (Option (SM.PC A Q I)) (Option I) :=
  ⟨some (.inl q), fun j => if j = some i then Tape.loaded none (s.map some)
    else Tape.loaded none []⟩

def left {J : Type} (R : ℕ) (_ : J) : ℤ := -(R : ℤ)
def right {J : Type} (R : ℕ) (_ : J) : ℤ := R

def initial (R : ℕ) (q : Q) (i : I) (s : List A) :=
  marked (left R) (right R) false (origin q i s)

/-- Reading the data track restores the original alphabet and the head coordinate. -/
def data {X : Type} (T : Tape (Symbol X)) : Tape X := ⟨T.pos, fun z => (T.view z).1⟩

@[simp] theorem data_markedTape {X : Type} (lo hi : ℤ) (T : Tape X) :
    data (markedTape lo hi T) = T := rfl

omit [Fintype I] in
theorem origin_within (R : ℕ) (q : Q) (i : I) (s : List A) :
    within (left R) (right R) (origin q i s) := by
  intro j
  have hp : ((origin q i s).tape j).pos = 0 := by
    by_cases hj : j = some i <;> simp [origin, hj, Tape.loaded]
  simp [left, right, hp]

/-- Every head remains in the very same interval throughout each trial,
regardless of its input, time budget, or whether the stack command is correct. -/
theorem prefix_within (R : ℕ) (q : Q) (i k : I) (s : List A) (g : SM.Rule A Q I)
    {t : ℕ} {z} (run : Trace (advance (rule k g)) (initial R q i s) t z) (j : Option I) :
    -(R : ℤ) ≤ (z.tape j).pos ∧ (z.tape j).pos ≤ R := by
  obtain ⟨x, tag, hx, rfl⟩ :=
    trace_within (SM.complete k g) (left R) (right R) (origin_within R q i s) run
  exact hx j

/-- Each guarded trial visits at most `K * (2R+1)` distinct cells on its `K`
physical tapes, including the input and the fresh output tape. -/
theorem visited (R budget : ℕ) (q : Q) (i k : I) (s : List A) (g : SM.Rule A Q I) :
    VisitsAtMost (rule k g) (initial R q i s) budget (Fintype.card (Option I) * (2*R+1)) := by
  have bound := visitsAtMost_of_common_fence (m := rule k g) (init := initial R q i s)
    (steps := budget) (-(R : ℤ)) (R : ℤ) (fun _ _ _ h j => prefix_within R q i k s g h j)
  convert bound using 2
  omega

/-- Across arbitrarily many restarts at zero, every covered cell of every
trial belongs to one box independent of the trial index and its tape contents. -/
theorem common_cover (R : ℕ) :
    ∃ cells : Finset (Option I × ℤ), cells.card = Fintype.card (Option I) * (2*R+1) ∧
      ∀ (q : Q) (i k : I) (s : List A) (g : SM.Rule A Q I) {t z},
        Trace (advance (rule k g)) (initial R q i s) t z →
          ∀ j, (j, (z.tape j).pos) ∈ cells := by
  classical
  refine ⟨Finset.univ ×ˢ Finset.Icc (-(R : ℤ)) (R : ℤ), ?_, ?_⟩
  · rw [Finset.card_product, Finset.card_univ, Int.card_Icc]
    congr 1
    omega
  · intro q i k s g t z h j
    simpa using prefix_within R q i k s g h j

/-- A sufficiently wide fence reproduces the released trace, its exact
transition count, the successful halt, and the complete answer on the data
track. The per-tape radius `2*H+2` is independent of the number of tapes. -/
theorem success {n H R : ℕ} {i k : I} {s : List A} {q : Q} {g : SM.Rule A Q I} {x}
    (call : Schoolbook.Segment g (SM.origin q i s) n x H) (stop : SM.advance g x = none)
    (room : 2*H+2 ≤ R) :
    let t := 2*n+1+(x.stack k).length
    ∃ z, Trace (advance (rule k g)) (initial R q i s) t z ∧
      advance (rule k g) z = none ∧ z.pc.1 = false ∧
      whole none ((x.stack k).map some) (data (z.tape none)) := by
  obtain ⟨last, cpu, halt, out, fence⟩ :=
    Schoolbook.complete_run_fence (k := k) call.run stop call.height
  let T := 2*n+1+(x.stack k).length
  have fits {u : ℕ} {v} (hu : u ≤ T) (h : Trace (advance (SM.complete k g)) (origin q i s) u v) :
      within (left R) (right R) v := by
    intro j
    have := fence u hu v h j
    change -(R : ℤ) ≤ _ ∧ _ ≤ (R : ℤ)
    omega
  refine ⟨marked (left R) (right R) false last,
    trace_marked _ _ _ cpu fits, ?_, rfl, out⟩
  simp only [rule, advance_marked (SM.complete k g) _ _ last (fits le_rfl cpu), halt, Option.map_none]

/-- Once the allotted budget includes the final halt test, the semantic
scheduler obtains the guarded physical result on its data track. -/
theorem try_success {n H R budget : ℕ} {i k : I} {s : List A} {q : Q} {g : SM.Rule A Q I} {x}
    (call : Schoolbook.Segment g (SM.origin q i s) n x H) (stop : SM.advance g x = none)
    (room : 2*H+2 ≤ R) (time : 2*n+1+(x.stack k).length < budget) :
    ∃ z, Schedule.tryFor (tapeTick (rule k g) (fun pc => !pc.1)) budget
        (initial R q i s) = some z ∧
      whole none ((x.stack k).map some) (data (z.tape none)) := by
  obtain ⟨z, run, halt, flag, answer⟩ := success (k := k) call stop room
  refine ⟨z, (Uniform.tapeTrial_iff _ _ _ _ _).2 ⟨_, time, run, halt, ?_⟩, answer⟩
  simp [flag]

end ChunkGuard

end NearSquareRoot
end Computability
end OAI

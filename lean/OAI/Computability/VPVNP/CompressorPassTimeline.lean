import OAI.Computability.VPVNP.CompressorBlockGroups
import OAI.Computability.VPVNP.CompressorExecutionCalendar

/-! # Physical pass intervals in the repeated block calendar

Each shrinking substep and degree refresh occupies its own window in the
fixed block script. Their absolute row intervals concatenate from the end
of the initial cursor setup through the exclusive calendar bound.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.PassTimeline

open Compression BlockPlanner

/-- An elementary pass of the repeated block script, either a bounded shrink index or the final
refresh. -/
inductive Pass (steps : ℕ) where
  | shrink (index : Fin steps)
  | refresh
  deriving DecidableEq

/-- An occurrence of an elementary pass together with its zero-based block number. -/
structure Located (steps : ℕ) where
  /-- Number of the block repetition containing this pass occurrence. -/
  block : ℕ
  /-- Shrink or refresh pass executed at this occurrence in the block. -/
  pass : Pass steps
  deriving DecidableEq

/-- Calendar phase label of the located pass, forgetting its block number. -/
def Located.phase {steps : ℕ} (z : Located steps) : ExecutionCalendar.Phase :=
  match z.pass with | .shrink i => .shrink i.val | .refresh => .refresh

/-- Pass occurrences within one specified block, listing all shrink indices before its refresh. -/
def oneBlock (steps t : ℕ) : List (Located steps) :=
  (List.finRange steps).map (fun i => ⟨t,.shrink i⟩) ++ [⟨t,.refresh⟩]

/-- Chronological pass occurrences across all block repetitions in the script. -/
def timeline (steps T : ℕ) : List (Located steps) := (List.range T).flatMap (oneBlock steps)

theorem oneBlock_phases (steps t : ℕ) : (oneBlock steps t).map Located.phase = ExecutionCalendar.oneBlock steps := by
  have h : (List.finRange steps).map Fin.val = List.range steps := by
    apply List.ext_getElem <;> simp
  unfold oneBlock ExecutionCalendar.oneBlock
  rw [List.map_append,← h,List.map_map,List.map_map]
  rfl

theorem timeline_phases (steps T : ℕ) : (timeline steps T).map Located.phase = ExecutionCalendar.blocks steps T := by
  induction T with
  | zero => rfl
  | succ t ih =>
    simp only [timeline,List.range_succ,List.flatMap_append,List.flatMap_singleton,List.map_append] at ih ⊢
    rw [ih,oneBlock_phases]
    unfold ExecutionCalendar.blocks
    rw [List.replicate_add,List.flatten_append]
    simp

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k}

/-- Concrete visits installed by this occurrence of the shrinking or refresh pass. -/
def Located.visits (z : Located S.steps) (B : S.Templates) : List Visit :=
  match z.pass with | .shrink i => BlockProgram.shrink B i | .refresh => BlockProgram.refresh B

/-- Contiguous script window occupied by the located pass's visits within its block. -/
def Located.window (z : Located S.steps) (B : S.Templates) :
    Window (BlockProgram.script B) (z.visits B) := by
  cases z with | mk t p =>
    cases p with
    | shrink i => exact BlockGroups.shrinkWindow B i
    | refresh => exact BlockGroups.refreshWindow B

/-- Absolute directory ordinal of the first visit, accounting for initialization, preceding
blocks, and the within-block offset. -/
def Located.first (z : Located S.steps) (B : S.Templates) :=
  (BlockProgram.script B).initial.length + z.block * (BlockProgram.script B).block.length + (z.window B).before.length

/-- First directory ordinal following the last visit of this pass occurrence. -/
def Located.finish (z : Located S.steps) (B : S.Templates) := z.first B + (z.visits B).length

/-- Each row of the interval is the actual indexed visit in the script;
its calendar level is the block at which the occurrence was located. -/
theorem Located.calendar_row (z : Located S.steps) (B : S.Templates) (i : Fin (z.visits B).length) :
    let A := BlockProgram.script B
    let j := (z.window B).index i
    A.visit j = (z.visits B)[i.val] ∧
    (Schedule.Online.calendar A.plan).phase (z.first B + i.val) = j.val ∧
    (Schedule.Online.calendar A.plan).level (z.first B + i.val) = z.block := by
  intro A j
  refine ⟨(z.window B).visit i,?_⟩
  have h := A.block_phase z.block ((z.window B).position i)
  simpa only [A,j,Located.first,Window.position,Window.index,Nat.add_assoc] using h

/-- The listed pass windows meet consecutively and span exactly the supplied start and finish
ordinals. -/
def Consecutive (B : S.Templates) (start : ℕ) : List (Located S.steps) → ℕ → Prop
  | [], stop => start = stop
  | z :: zs, stop => z.first B = start ∧ Consecutive B (z.finish B) zs stop

theorem Consecutive.append {B : S.Templates} {start middle stop : ℕ} {xs ys : List (Located S.steps)}
    (h : Consecutive B start xs middle) (h' : Consecutive B middle ys stop) :
    Consecutive B start (xs++ys) stop := by
  induction xs generalizing start with
  | nil => change start = middle at h; subst start; exact h'
  | cons z zs ih => exact ⟨h.1,ih h.2⟩

private def blockStart (B : S.Templates) (t : ℕ) :=
  (BlockProgram.script B).initial.length + t * (BlockProgram.script B).block.length

private def shrinkPrefix (B : S.Templates) (j : ℕ) := ((List.finRange S.steps).take j).flatMap (BlockProgram.shrink B)

set_option maxHeartbeats 800000 in
private theorem shrink_consecutive (B : S.Templates) (t j : ℕ) (hj : j ≤ S.steps) :
    Consecutive B (blockStart B t) (((List.finRange S.steps).take j).map (fun i => ⟨t,.shrink i⟩))
      (blockStart B t + (shrinkPrefix B j).length) := by
  induction j with
  | zero => simp only [List.take_zero,List.map_nil,shrinkPrefix,List.flatMap_nil,List.length_nil,Nat.add_zero,Consecutive]
  | succ j ih =>
    let i : Fin S.steps := ⟨j,hj⟩
    have htake : (List.finRange S.steps).take (j+1) = (List.finRange S.steps).take j ++ [i] := by
      rw [List.take_succ_eq_append_getElem (by simpa using hj)]
      simp [i]
    have hend : (shrinkPrefix B (j+1)).length = (shrinkPrefix B j).length + (BlockProgram.shrink B i).length := by
      simp only [shrinkPrefix,htake,List.flatMap_append,List.flatMap_singleton,List.length_append]
    rw [htake,List.map_append,hend,← Nat.add_assoc]
    apply Consecutive.append (ih (Nat.le_of_succ_le hj))
    exact ⟨rfl,rfl⟩

theorem oneBlock_consecutive (B : S.Templates) (t : ℕ) :
    Consecutive B (blockStart B t) (oneBlock S.steps t) (blockStart B (t+1)) := by
  have h := shrink_consecutive B t S.steps le_rfl
  have htake : (List.finRange S.steps).take S.steps = List.finRange S.steps := by simp
  simp only [htake,shrinkPrefix] at h
  apply Consecutive.append h
  refine ⟨rfl,?_⟩
  change blockStart B t + ((List.finRange S.steps).flatMap (BlockProgram.shrink B)).length +
    (BlockProgram.refresh B).length = blockStart B (t+1)
  simp [blockStart,BlockProgram.script,BlockProgram.block,Nat.add_mul,Nat.add_assoc]

/-- The fold of successive half-open pass intervals, with the actual
calendar bound even when the block is never entered. -/
theorem timeline_consecutive (B : S.Templates) (T : ℕ) :
    Consecutive B (BlockProgram.script B).initial.length (timeline S.steps T)
      ((Schedule.Online.calendar (BlockProgram.script B).plan).total T) := by
  rw [(BlockProgram.script B).calendar_total]
  change Consecutive B (BlockProgram.script B).initial.length (timeline S.steps T) (blockStart B T)
  induction T with
  | zero => simp [timeline,Consecutive,blockStart]
  | succ t ih =>
    simp only [timeline,List.range_succ,List.flatMap_append,List.flatMap_singleton] at ih ⊢
    exact ih.append (oneBlock_consecutive B t)

/-- The state-dependent mathematical execution follows this same list of
located visits on every sequence of terms. -/
theorem execute_follows_timeline (B : S.Templates) {R : Type*} [CommRing R] (f : B.Entry → R)
    (hf : B.IsSolution f) (T : ℕ) {n : ℕ} (h : T*S.laneBits ≤ n) (X : State (S.degreeExponent 0) n) :
    ExecutionCalendar.Follows (B.execute f hf T h X) (executeOrigins B f hf T h X)
      ((timeline S.steps T).map Located.phase) := by
  rw [timeline_phases]
  exact ExecutionCalendar.execute_follows T h X

end CompressorRecords.PassTimeline

end

end VPVNP
end Computability
end OAI

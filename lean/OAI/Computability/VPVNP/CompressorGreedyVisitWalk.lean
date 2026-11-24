import OAI.Computability.VPVNP.CompressorGreedyPrepareProgress
import OAI.Computability.VPVNP.CompressorGreedyReadProgress
import OAI.Computability.VPVNP.CompressorGreedyLevelPlan
import OAI.Computability.VPVNP.CompressorRecordsShrinkGreedy
import OAI.Computability.VPVNP.CompressorSourceOnline
import OAI.Computability.VPVNP.CompressorSourceWalk

/-!
# Six consecutive native visits that compute the shrinking directory

The tag projection and zero publication precede the color directory. Both
offset visits begin in the post-memory of the color reader. Each packet keeps
its exact native program, public parameters, cursor interval and choice tapes.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.GreedyVisit

open BurstRAM PrivateRAM Compression BlockPlanner PhaseRecipe Greedy GreedyArena
open scoped Fin.CommRing

/-- The six native stages used to build the shrinking level's greedy color and tag directories. -/
inductive Stage | extract | zero | colorPrepare | colorRead | tagPrepare | tagRead
  deriving DecidableEq

/-- Execution order of the greedy stages, beginning with shift extraction and ending with the
tag scan. -/
def stages : List Stage := [.extract,.zero,.colorPrepare,.colorRead,.tagPrepare,.tagRead]

instance : Fintype Stage := ⟨stages.toFinset, by intro j; cases j <;> decide⟩

/-- Planner visit implementing a greedy stage at the specified level and scratch origin. -/
def visit (shape : DescriptorSpace.Shape) (step a : ℕ) (origin : Expr) : Stage → BlockPlanner.Visit
  | .extract => GreedyLevelPlan.extractShifts shape step a origin
  | .zero => GreedyLevelPlan.publishZero shape step a origin
  | .colorPrepare => GreedyLevelPlan.colorPrepare shape step a origin
  | .colorRead => GreedyLevelPlan.colorRead step a origin
  | .tagPrepare => GreedyLevelPlan.tagPrepare shape step a origin
  | .tagRead => GreedyLevelPlan.tagRead step a origin

theorem visits_eq (shape : DescriptorSpace.Shape) (step a : ℕ) (origin : Expr) :
    stages.map (visit shape step a origin) = GreedyLevelPlan.visits shape step a origin := rfl

variable {w a g z : ℕ} {X : GreedyArena.ShrinkingState a g} {T : IncidenceDirectory w}
  {m : Memory w} (r : GreedyArena.Run X T z m)

private abbrev n := Fintype.card X.Base
private abbrev project := projectionWords T z (n (X := X)) a g
private abbrev L := colorLayout w z (n (X := X)) a r.room
private abbrev K := tagLayout w z (n (X := X)) a r.room

/-- Initial cursor for a greedy stage. Record readers start at their first record address and
the other stages start at zero. -/
def start : Stage → Word w
  | .colorRead => (L r).base 0
  | .tagRead => (K r).base 0
  | _ => 0

/-- Exclusive cursor bound for the stage, expressed as a row count or the address past the
final walk record. -/
def stop : Stage → Word w
  | .extract => ((n (X := X) * 2^a : ℕ) : Word w)
  | .zero => 1
  | .colorPrepare | .tagPrepare => (n (X := X) : Word w)
  | .colorRead => (L r).base (n (X := X))
  | .tagRead => (K r).base (n (X := X))

/-- Private instruction budget for one worker call of the given greedy stage and degree
exponent. -/
def fuel (a : ℕ) : Stage → ℕ
  | .extract => 14
  | .zero => 5
  | .colorPrepare => 1 + (Relocated.prepareCode (colorOperandRows (2^a))).length
  | .tagPrepare => 1 + (Relocated.prepareCode (tagOperandRows (2^a))).length
  | .colorRead => 1 + (visitCode 1 (2*2^a)).length
  | .tagRead => 1 + (visitCode 4 (WalkLayout.tagCount (2^a))).length

theorem fuel_pos (j : Stage) : 0 < fuel a j := by cases j <;> simp [fuel]

/-- Empty choice tapes for the deterministic greedy calls, with one tape per row visited by the
stage. -/
def choices (X : GreedyArena.ShrinkingState a g) : Stage → List (List Bool)
  | .extract => List.replicate (Fintype.card X.Base * 2^a) []
  | .zero => [[]]
  | _ => List.replicate (Fintype.card X.Base) []

/-- Concrete public operands of the installed worker, obtained from the greedy arena and its
incidence tables. -/
def params (shape : DescriptorSpace.Shape) (step : ℕ) (origin : Expr) (j : Stage) :
    Fin (visit shape step a origin j).worker.params → Word w :=
  match j with
  | .extract | .zero => project (X := X) (T := T) (z := z)
  | .colorPrepare => Relocated.publicWords (2^a) (L r) (colorTables T z (n (X := X)) a)
  | .colorRead | .tagRead => Fin.elim0
  | .tagPrepare => Relocated.publicWords (2^a) (K r) (tagTables T z (n (X := X)) a)

/-- These equalities identify the worker ABI at any memory in which the
descriptor parameters have their specified values. -/
theorem values {shape : DescriptorSpace.Shape} {step : ℕ} {origin : Expr} {pub : Fin 5 → Word w}
    {state : Word w} {input : Memory w}
    (h : GreedyLevelPlan.Reads shape step a origin pub state input (n (X := X)) g z T) (j : Stage) :
    let v := visit shape step a origin j
    v.initial.eval pub state input = start r j ∧ v.stop.eval pub state input = stop r j ∧
      (fun i => (v.params i).eval pub state input) = params r shape step origin j := by
  cases j with
  | extract => exact GreedyLevelPlan.extractShifts_values h
  | zero => exact GreedyLevelPlan.publishZero_values h
  | colorPrepare => exact GreedyLevelPlan.colorPrepare_values h r.room
  | colorRead => exact GreedyLevelPlan.colorRead_values h r.room
  | tagPrepare => exact GreedyLevelPlan.tagPrepare_values h r.room
  | tagRead => exact GreedyLevelPlan.tagRead_values h r.room

/-- Evidence that the native stage produces the stated reports from its input memory and
advances to its prescribed stop cursor. -/
structure Source (shape : DescriptorSpace.Shape) (step : ℕ) (origin : Expr) (j : Stage)
    (input : Memory w) (reports : List (Report w)) : Prop where
  native : runSegment (((visit shape step a origin j).worker.table.instantiate w (params r shape step origin j)).program)
    (fuel a j) (some (start r j)) input (choices X j) = some reports
  progress : SourceOnline.Progress (stop r j) (start r j) reports

private theorem projection_progress (p : Fin 5 → Word w) (i len : ℕ) (input : Memory w) (fit : i+len < 2^w) :
    SourceOnline.Progress ((i+len : ℕ) : Word w) (i : Word w) (ShrinkTagColumn.scan p i len input) := by
  induction len generalizing i input with
  | zero => exact .done le_rfl
  | succ len ih =>
    have hnext := ih (i+1) (after input (ShrinkTagColumn.row p (i : Word w) input).events) (by omega)
    rw [show i+1+len = i+(len+1) by omega] at hnext
    refine .next (next := ((i+1 : ℕ) : Word w)) ?_ ?_ hnext
    · change i%(2^w) < (i+(len+1))%(2^w)
      rw [Nat.mod_eq_of_lt (by omega : i < 2^w),Nat.mod_eq_of_lt fit]; omega
    · simp [ShrinkTagColumn.row]

/-- Chronological reports emitted by the chosen stage of the greedy shrinking pass. -/
def packetReports : Stage → List (Report w)
  | .extract => ShrinkTagColumn.scan (project (X := X) (T := T) (z := z)) 0 ((n (X := X))*2^a) m
  | .zero => [ShrinkTagColumn.zeroRow (project (X := X) (T := T) (z := z))]
  | .colorPrepare => r.color.prep
  | .colorRead => r.color.reads
  | .tagPrepare => r.offsets.prep
  | .tagRead => r.offsets.reads

/-- Input memory for the given stage after applying the reports of its predecessors in the
greedy walk. -/
def packetInput : Stage → Memory w
  | .extract => m
  | .zero => after m (eventLog (packetReports r .extract))
  | .colorPrepare => projectedMemory X T z m
  | .colorRead => after (projectedMemory X T z m) (eventLog r.color.prep)
  | .tagPrepare => r.color.post
  | .tagRead => after r.color.post (eventLog r.offsets.prep)

private theorem zeroOutput :
    after (packetInput r .zero) (eventLog (packetReports r .zero)) = packetInput r .colorPrepare :=
  (SourceWalk.after_append m (packetReports r .extract) (packetReports r .zero)).symm

theorem source_at (shape : DescriptorSpace.Shape) (step : ℕ) (origin : Expr) (j : Stage) :
    Source r shape step origin j (packetInput r j) (packetReports r j) := by
  cases j with
  | extract =>
    refine ⟨r.projection.extractRun,?_⟩
    have room := r.room
    change GreedyArena.shiftBase z (n (X := X)) a + (n (X := X))*2^a + 1 < 2^w at room
    simpa [stop,start,packetReports] using projection_progress (project (X := X) (T := T) (z := z))
      0 ((n (X := X))*2^a) m (by omega)
  | zero =>
    have hpos : 1 < 2^w := by
      have room := r.room
      change GreedyArena.shiftBase z (n (X := X)) a + (n (X := X))*2^a + 1 < 2^w at room
      omega
    refine ⟨r.projection.zeroRun,.next (next := 1) ?_ rfl (.done le_rfl)⟩
    change 0%(2^w) < 1%(2^w); rw [Nat.zero_mod,Nat.mod_eq_of_lt hpos]; decide
  | colorPrepare => exact ⟨r.color.prepRun,r.color_prepare_progress⟩
  | colorRead => exact ⟨r.color.readRun,r.color_read_progress⟩
  | tagPrepare => exact ⟨r.offsets.prepRun,r.tag_prepare_progress⟩
  | tagRead => exact ⟨r.offsets.readRun,r.tag_read_progress⟩

/-- Each stage names its own input memory and report slice in the walk. -/
theorem indexed_walk (shape : DescriptorSpace.Shape) (step : ℕ) (origin : Expr) :
    SourceWalk (fun j input rs => input = packetInput r j ∧ rs = packetReports r j ∧
      Source r shape step origin j input rs) stages m r.reports := by
  let P := fun j input rs => input = packetInput r j ∧ rs = packetReports r j ∧ Source r shape step origin j input rs
  have row (j : Stage) : P j (packetInput r j) (packetReports r j) := ⟨rfl,rfl,source_at r shape step origin j⟩
  have rest : SourceWalk P [.colorPrepare,.colorRead,.tagPrepare,.tagRead] (packetInput r .colorPrepare)
      (r.color.prep ++ (r.color.reads ++ (r.offsets.prep ++ r.offsets.reads))) :=
    SourceWalk.next (row .colorPrepare) (SourceWalk.next (row .colorRead)
      (SourceWalk.next (row .tagPrepare) (SourceWalk.singleton (row .tagRead))))
  rw [← zeroOutput r] at rest
  have whole := SourceWalk.next (row .extract) (SourceWalk.next (row .zero) rest)
  change SourceWalk P stages m (((((packetReports r .extract ++ packetReports r .zero) ++
    r.color.prep) ++ r.color.reads) ++ r.offsets.prep) ++ r.offsets.reads)
  simp only [List.append_assoc]
  exact whole

/-- Six actual native segments, including the guard proof for every call. -/
theorem walk (shape : DescriptorSpace.Shape) (step : ℕ) (origin : Expr) :
    SourceWalk (Source r shape step origin) stages m r.reports := by
  have forget {js input rs} (h : SourceWalk (fun j input rs => input = packetInput r j ∧
      rs = packetReports r j ∧ Source r shape step origin j input rs) js input rs) :
      SourceWalk (Source r shape step origin) js input rs := by
    induction h with
    | done => exact .done _
    | next head _ tail => exact .next head.2.2 tail
  exact forget (indexed_walk r shape step origin)

end CompressorRecords.GreedyVisit

end VPVNP
end Computability
end OAI

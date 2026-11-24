import OAI.Computability.VPVNP.CompressorScheduledTrace
import OAI.Computability.VPVNP.CompressorTimelineDepth
import OAI.Computability.VPVNP.CompressorPrefixLevelScale

/-! # Applying the descriptor induction to the paper's iterated compressor

The actual compression tree and its native table share their chronological
block and pass indices. Partial branches use the proved size bounds on
their current graph, and the completed path gives the native source log
and the retained mathematical levels at the same terminal memory.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section
namespace CompressorRecords.ScheduledTrace

open BurstRAM Compression BranchSegments PassTimeline PairSimulation.LocalHistory
attribute [local irreducible] BlockProgram.script

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} {B : S.Templates}
variable {R : Type*} [CommRing R] {f : B.Entry → R} {hf : B.IsSolution f}
variable {w cap small rate total T P M : ℕ} {pub : Fin 11 → Word w} {pitch : Word w}
variable {resident : Resident B f hf w}
local notation "A" => BlockProgram.script B

/-- The native per-pass constructor is needed only in its true block and
substep and only for graph sizes permitted by the initial allocation. -/
abbrev LocatedRuns (resident : Resident B f hf w) (pub : Fin 11 → Word w) (pitch : Word w)
    (total cap small rate T P M : ℕ) :=
  ∀ {a g b n : ℕ} {X : State a g} {p : StatePass R X b n} (o : PassOrigin B f hf p)
    (encode : p.step.Choice → List Bool) (loc : Located S.steps) (past : List (SelectedLevel B f hf))
    (m : Memory w), ExecutionCalendar.kind o = loc.phase → loc.block < T → past.length = loc.depth →
    X.positions ≤ P → X.maxWireWidth ≤ M →
    (∀ i, (p.next i).positions ≤ P ∧ (p.next i).maxWireWidth ≤ M) → Boundary resident pub pitch total (loc.first B) past X m →
    Nonempty (PassRun resident pub pitch total cap small rate loc o encode past m)

private theorem runTree_of_located {a g b n : ℕ} {X : State a g}
    (build : LocatedRuns resident pub pitch total cap small rate T P M)
    (E : StateExecution R b n X) (o : PassOrigins B f hf E) (W : E.MapWitnesses f) (r : ExecutionReaders E W)
    (xs : List (Located S.steps)) (past : List (SelectedLevel B f hf))
    (depth : Numbered past.length xs) (inside : ∀ loc ∈ xs, loc.block < T)
    (order : ExecutionCalendar.Follows E o (xs.map Located.phase)) (size : PrefixLevelScale.Within P M E) :
    RunTree resident pub pitch total cap small rate E o W r xs past := by
  induction E generalizing xs past with
  | done => trivial
  | more p tail ih =>
    cases xs with
    | nil => exact order.elim
    | cons loc rest =>
      refine ⟨fun phase m ready => build o.1 r.1.select.encode loc past m phase (inside loc List.mem_cons_self)
        depth.head.symm size.1 size.2.1 (fun i => (size.2.2 i).current) ready,?_⟩
      intro i
      apply ih i (o := o.2 i) (W := W.2 i) (r := r.2 i) (xs := rest)
      · simpa only [List.length_append,List.length_singleton] using depth.tail
      · exact fun loc hl => inside loc (List.mem_cons_of_mem _ hl)
      · exact order.2 i
      · exact size.2.2 i

variable {lanes : ℕ} (h : T*S.laneBits ≤ lanes) (X : State (S.degreeExponent 0) lanes)

/-- The term readers for the scheduled execution obtained by repeating the block readers across
all selected blocks. -/
noncomputable abbrev nativeReaders :=
  repeatReaders (blockReaders B f hf) _ T lanes (Nat.add_sub_of_le h).symm X

local notation "sel" => B.execute f hf T h X
local notation "origins" => executeOrigins B f hf T h X
local notation "stages" => timeline S.steps T
local notation "lastRow" => Schedule.LevelCalendar.Calendar.total (Schedule.Online.calendar (BlockPlanner.Script.plan A)) T

/-- Recursion on the actual chosen compression execution, beginning just
after its four deterministic cursor initialization rows. -/
theorem execute (m : Memory w)
    (bounds : Schedule.Online.Run.ControlBounds (BlockPlanner.Script.plan A) cap (w := w))
    (smallBounds : Schedule.Online.Run.ControlBounds (BlockPlanner.Script.plan A) small (w := w))
    (passes : RunTree resident pub pitch lastRow cap small rate sel origins _
      (nativeReaders (B := B) (f := f) (hf := hf) h X) stages [])
    (ready : Boundary resident pub pitch lastRow (BlockPlanner.Script.initial A).length [] X m) :
    Nonempty (Result resident pub pitch lastRow cap small (T*(S.steps+1)*rate+4)
      sel origins _ (nativeReaders (B := B) (f := f) (hf := hf) h X) [] (some 0) m) := by
  rw [← timeline_length S.steps T]
  exact iterate bounds smallBounds sel origins _ _ [] _ _ m rfl stages (execute_follows_timeline B f hf T h X)
    (timeline_consecutive B T) passes ready

theorem execute_of_local (m : Memory w)
    (bounds : Schedule.Online.Run.ControlBounds (BlockPlanner.Script.plan A) cap (w := w))
    (smallBounds : Schedule.Online.Run.ControlBounds (BlockPlanner.Script.plan A) small (w := w))
    (build : LocatedRuns resident pub pitch lastRow cap small rate T P M)
    (size : PrefixLevelScale.Within P M sel)
    (ready : Boundary resident pub pitch lastRow (BlockPlanner.Script.initial A).length [] X m) :
    Nonempty (Result resident pub pitch lastRow cap small (T*(S.steps+1)*rate+4)
      sel origins _ (nativeReaders (B := B) (f := f) (hf := hf) h X) [] (some 0) m) := by
  apply execute h X m bounds smallBounds _ ready
  exact runTree_of_located build sel origins _ _ stages [] (timeline_numbered S.steps T)
    (fun _ hl => block_lt_of_mem hl) (execute_follows_timeline B f hf T h X) size

end CompressorRecords.ScheduledTrace

end

end VPVNP
end Computability
end OAI

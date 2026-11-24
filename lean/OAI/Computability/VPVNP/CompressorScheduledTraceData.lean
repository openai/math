import OAI.Computability.VPVNP.CompressorPassTimeline
import OAI.Computability.VPVNP.CompressorPrefixFrames
import OAI.Computability.VPVNP.CompressorWorkspaceCore

/-! # Threading the physical descriptor program through the selected execution

The fixed finite table uses the calendar of the compiled block program.
At each shrinking or refresh pass the next interval starts at its proved
absolute ordinal, in the memory returned on that choice. The final call
uses the true exclusive bound. The construction retains the full selected
history, the source reports at their private clock, and the low-address
frame even on successful partial streams which cannot extend to acceptance.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section
namespace CompressorRecords.ScheduledTrace
open BurstRAM Compression BranchSegments PassTimeline PairSimulation.LocalHistory
open scoped Fin.CommRing
attribute [local irreducible] BlockProgram.script
open private collectLevels from OAI.Computability.VPVNP.CompressorExecutionLevels

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} {B : S.Templates}
variable {R : Type*} [CommRing R] {f : B.Entry → R} {hf : B.IsSolution f}
variable {w cap small rate total : ℕ} {pub : Fin 11 → Word w} {pitch : Word w}

local notation "script" => BlockProgram.script B
local notation "pt" => Workspace.ports (Schedule.arity (BlockPlanner.Script.catalog (BlockProgram.script B))) (pub 2)
local notation "outer" => OnlineWorkspace.program (BlockPlanner.Script.plan (BlockProgram.script B)) pub
local notation "lo" => Fin.val (pub 2)+6

/-- The application-specific stored graph and the records of all previously
selected levels. The controller fields are tracked separately. -/
abbrev Resident (B : S.Templates) (f : B.Entry → R) (hf : B.IsSolution f) (w : ℕ) :=
  List (SelectedLevel B f hf) → {a g : ℕ} → State a g → Memory w → Prop

variable {resident : Resident B f hf w}

/-- Physical state shared by the preceding pass, the next recipe and the
eventual terminal traversal. -/
structure Boundary (resident : Resident B f hf w) (pub : Fin 11 → Word w) (pitch : Word w)
    (total ordinal : ℕ) (past : List (SelectedLevel B f hf)) {a g : ℕ} (X : State a g) (m : Memory w) : Prop where
  bank : Workspace.Installed (Schedule.arity (BlockProgram.script B).catalog) (pub 2) m
  tag : m (Workspace.ports (Schedule.arity (BlockProgram.script B).catalog) (pub 2)).tag.val =
    LiveStageLink.tagWord w (Schedule.Online.calendarIndex (BlockProgram.script B).size (BlockProgram.script B).size)
  ordinalValue : (m (Workspace.ports (Schedule.arity (BlockProgram.script B).catalog) (pub 2)).ordinal.val).val = ordinal
  totalValue : (m (Workspace.ports (Schedule.arity (BlockProgram.script B).catalog) (pub 2)).rows.val).val = total
  stride : m ((Workspace.ports (Schedule.arity (BlockProgram.script B).catalog) (pub 2)).directory-1).val = pitch
  stored : resident past X m

/-- Package a pass, its origin, the selected term, and that term's encoded tape as one history
level. -/
def level {a g b n : ℕ} {X : State a g} {p : StatePass R X b n}
    (o : PassOrigin B f hf p) (encode : p.step.Choice → List Bool) (i : p.step.Choice) : SelectedLevel B f hf :=
  ⟨a,g,b,n,X,p,o,i,encode i⟩

/-- Evidence for one physical interval of the repeating calendar. The
reports and memory of each branch are those of the concrete cut. -/
structure PassRun (resident : Resident B f hf w) (pub : Fin 11 → Word w) (pitch : Word w)
    (total cap small rate : ℕ) (loc : Located S.steps) {a g b n : ℕ} {X : State a g} {p : StatePass R X b n}
    (o : PassOrigin B f hf p) (encode : p.step.Choice → List Bool) (past : List (SelectedLevel B f hf)) (m : Memory w) where
  /-- Native pass segments indexed by term choice, with disjoint tape prefixes covering every
  halting run. -/
  cut : Cut (OnlineWorkspace.program (BlockProgram.script B).plan pub) (cap+24) (some 0) m p.step.Choice
  frame : cut.PrefixFrame ((pub 2).val+6)
  state : ∀ i, (cut.part i).state = some 0
  /-- Source reports recovered from the native segment for each choice of the current pass. -/
  source : ∀ i, OnlineWorkspace.Core (clock := cap+24) (BlockProgram.script B) pub (cut.part i) small
  cost : ∀ i, RAMBuckets.cost Report.probes (source i).logs ≤ rate
  next : ∀ i, Boundary resident pub pitch total (loc.finish B) (past++[level o encode i]) (p.next i) (cut.part i).memory

/-- Local constructors are needed only on the actual mathematical tree,
with the concrete reader, earlier selected history and physical window.
No extension of a prefix to a complete accepting branch is required. -/
def RunTree (resident : Resident B f hf w) (pub : Fin 11 → Word w) (pitch : Word w)
    (total cap small rate : ℕ) {a g b n : ℕ} {X : State a g} :
    (E : StateExecution R b n X) → PassOrigins B f hf E → (W : E.MapWitnesses f) →
    ExecutionReaders E W → List (Located S.steps) → List (SelectedLevel B f hf) → Prop
  | .done _, _, _, _, _, _ => True
  | .more _ _, _, _, _, [], _ => False
  | @StateExecution.more _ _ _ _ _ _ _ _ X _ tail, o, W, r, loc::rest, past =>
    (ExecutionCalendar.kind o.1 = loc.phase → ∀ m,
      Boundary resident pub pitch total (loc.first B) past X m →
      Nonempty (PassRun resident pub pitch total cap small rate loc o.1 r.1.select.encode past m)) ∧
      ∀ i, RunTree resident pub pitch total cap small rate (tail i) (o.2 i) (W.2 i) (r.2 i) rest
        (past++[level o.1 r.1.select.encode i])

variable {a g b n : ℕ} {X : State a g} {E : StateExecution R b n X}

/-- All selected mathematical histories are retained in their real final
memories. Work counts visits with multiplicity, including repeated states. -/
structure Result (resident : Resident B f hf w) (pub : Fin 11 → Word w) (pitch : Word w)
    (total cap small budget : ℕ) (E : StateExecution R b n X) (o : PassOrigins B f hf E)
    (W : E.MapWitnesses f) (r : ExecutionReaders E W) (past : List (SelectedLevel B f hf))
    (st : Option (Word w)) (m : Memory w) where
  /-- Native execution trace for the scheduled descriptor program, indexed by branches of the
  compression execution. -/
  trace : ExecutionTrace (OnlineWorkspace.program (BlockProgram.script B).plan pub) (cap+24) E st m
  frame : trace.Framed ((pub 2).val+6)
  /-- Source reports underlying the native trace segment for each complete branch. -/
  source : ∀ z, OnlineWorkspace.Core (clock := cap+24) (BlockProgram.script B) pub (trace.cut.part z) small
  cost : ∀ z, RAMBuckets.cost Report.probes (source z).logs ≤ budget
  final : ∀ z, Boundary resident pub pitch total total (past++collectLevels B f hf E W r o z)
    (E.finalState z) (trace.cut.part z).memory

end CompressorRecords.ScheduledTrace

end

end VPVNP
end Computability
end OAI

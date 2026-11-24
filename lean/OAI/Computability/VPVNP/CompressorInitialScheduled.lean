import OAI.Computability.VPVNP.CompressorInitialPhysical
import OAI.Computability.VPVNP.CompressorDeterministicGroup

/-! # The four initial descriptor rows as one scheduled native interval

The data reports are precisely the initial cursor initialization logs, with
the calendar and planner calls charged at their actual cost. The source runs
at its private clock, and the framed machine can run with a larger clock.
Every prefix, including a successful prefix with no accepting continuation,
preserves the six-pointer bank and all lower addresses.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section
namespace CompressorRecords.ScheduledTrace

open BurstRAM Compression DescriptorSpace BlockPlanner Schedule BranchSegments SourceTransport
open scoped Fin.CommRing
open private count_lt from OAI.Computability.VPVNP.CompressorInitialPhysical
open private interval_mono final_tag from OAI.Computability.VPVNP.CompressorDeterministicGroup

variable {w : ℕ} {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
variable (base positions blocks cap small b l width n : ℕ) (pub : Fin 11 → Word w) (m : Memory w)
local notation "A" => BlockProgram.script B
local notation "L" => BlockProgram.layout B base positions blocks
local notation "a₀" => S.degreeExponent 0
local notation "pt" => Workspace.ports (arity (Script.catalog (BlockProgram.script B))) (pub 2)

/-- Native work before the first selected row, including four calendar,
recipe, launch and worker-close calls and the actual source data probes. -/
def initialCost (script : Script) (data : List (Report w)) :=
  RAMBuckets.cost Report.probes data * (arity script.catalog+3) + 4*(Online.Run.maxReads script.plan+4*arity script.catalog+26)

/-- The four deterministic visits, their native cost, and the live memory supplied to ordinal four. -/
structure InitialInterval where
  /-- The actual workspace-framed run of the four visits. -/
  interval : QuietInterval A pub cap small (some 0) m
  agrees : Agree (levelStart L 0 ≤ ·) (BlockInitialPackets.post L a₀ b l width m) interval.segment.memory
  bank : Workspace.Installed (arity (A).catalog) (pub 2) interval.segment.memory
  tag : interval.segment.memory (pt).tag.val = LiveStageLink.tagWord w (Online.calendarIndex (A).size (A).size)
  ordinal : (interval.segment.memory (pt).ordinal.val).val = 4
  total : (interval.segment.memory (pt).rows.val).val = directoryRows L
  stride : interval.segment.memory ((pt).directory-1).val = (levelWords L : Word w)
  cost : RAMBuckets.cost Report.probes interval.source.logs ≤ initialCost A (BlockInitialPackets.logs L a₀ b l width m)

/-- Run the four cursor visits in the exact incoming RAM memory. The
recovered controller fields are ready for ordinal four. -/
theorem initialInterval (X : State a₀ l) (fit : endAddress L < 2^w) (workspace : (pub 2).val = base)
    (ready : OnlineWorkspace.Ready (A).size (L).shape.arity (pub 2) (directoryRows L) (levelWords L) m)
    (cursor : BlockStartupPrefix.Resident L a₀ b l width n (pub 2) m X)
    (clock : InitialScriptPackets.budget A (BlockProgram.layout B 0 0 0) a₀ ≤ small)
    (leClock : small ≤ cap) (bounds : Online.Run.ControlBounds (A).plan small (w := w)) :
    Nonempty (InitialInterval B base positions blocks cap small b l width pub m) := by
  let script := BlockProgram.script B
  let alloc := BlockProgram.layout B base positions blocks
  have arityEq : arity script.catalog = alloc.shape.arity := rfl
  have positive : 0 < alloc.levels := by change 0 < 1+(S.steps+1)*blocks; omega
  have rows : directoryRows alloc = 4+blocks*script.block.length :=
    (BlockProgram.directory_rows B base positions blocks).trans (script.calendar_total blocks)
  have tag : m (pt).tag.val = LiveStageLink.tagWord w (Online.calendarIndex script.size script.size) := by
    change m (pt).tag.val = ((script.size+1+0 : ℕ) : Word w)
    rw [Nat.add_zero]
    exact ready.tag
  have total : (m (pt).rows.val).val = directoryRows alloc := by
    rw [show m (pt).rows.val = (directoryRows alloc : Word w) from ready.count]
    exact Nat.mod_eq_of_lt (count_lt B base positions blocks fit)
  obtain ⟨steps,v,phases,data,agree,ordinal,cnt,pitch,stable⟩ := InitialOnline.interval script alloc (pub 2)
    a₀ b l width small ((InitialScriptPackets.budget_fixed B base positions blocks a₀) ▸ clock) arityEq workspace
    positive (by change 14 ≤ 54; decide) fit (InitialScriptPackets.actual_order B base positions blocks)
    m cursor.walk (by omega) ready.ordinal total tag ready.pitch
  have big : Online.Run.ControlBounds script.plan cap (w := w) :=
    ⟨bounds.tags,bounds.calendar.trans leClock,bounds.launch.trans leClock⟩
  have vBig := interval_mono v leClock
  let seg := OnlineWorkspace.intervalSegment script pub big tag steps vBig stable ready.bank
  let source : OnlineWorkspace.Core script pub seg small :=
    ⟨Online.Run.intervalLog script.plan pt m steps,(Online.Run.intervalSegment script.plan pt (state := 0) bounds tag steps v).run,rfl⟩
  let interval : QuietInterval script pub cap small (some 0) m :=
    ⟨seg,InitialConverse.quiet script pub alloc a₀ b l width small m steps v data,
     OnlineWorkspace.intervalSegment_stable ..,OnlineWorkspace.intervalSegment_state ..,source⟩
  have mem : interval.segment.memory = Online.Run.finalMemory (C := script.catalog) pt m steps :=
    OnlineWorkspace.intervalSegment_memory script pub big tag steps vBig stable ready.bank
  have num : steps.length = 4 := by
    have len := congrArg List.length phases
    simp only [List.length_map, InitialScriptPackets.indices, List.length_ofFn] at len
    exact len
  refine ⟨⟨interval,mem.symm ▸ agree,OnlineWorkspace.intervalSegment_bank script pub big tag steps vBig stable ready.bank,mem.symm ▸ final_tag tag,
    mem.symm ▸ ordinal,mem.symm ▸ (congrArg Fin.val cnt).trans total,mem.symm ▸ pitch.trans ready.pitch,?_⟩⟩
  have actual := Online.Run.interval_cost_bound script.plan pt steps m v
  have logs : steps.flatMap (fun s => s.row.reports) = BlockInitialPackets.logs alloc a₀ b l width m := data
  rw [Online.Run.sourceCost_eq_flatMap,logs,num] at actual
  exact actual

end CompressorRecords.ScheduledTrace

end

end VPVNP
end Computability
end OAI

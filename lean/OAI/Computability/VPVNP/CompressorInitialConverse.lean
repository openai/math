import OAI.Computability.VPVNP.CompressorBlockInitialPackets
import OAI.Computability.VPVNP.CompressorWorkspaceBranchCut
import OAI.Computability.VPVNP.CompressorSourceBankFrame

/-!
# Forced physical execution of the initial cursor visits

All four data workers consume only empty choice strings. Calendar, planner,
launcher and closing calls also consume empty strings. Any accepted framed
run therefore has exactly the native initial reports and memory before the
next compressor phase. With four directory rows the next calendar call is
the final accepting call.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.InitialConverse

open BurstRAM BlockPlanner DescriptorSpace BranchSegments Schedule
open scoped Fin.CommRing

variable {w : ℕ} (A : Script) (pub : Fin 11 → Word w)
local notation "pt" => Workspace.ports (arity A.catalog) (pub 2)
local notation "tag" => LiveStageLink.tagWord w (Online.calendarIndex A.size A.size)
local notation "P" => OnlineWorkspace.program A.plan pub

private theorem bits_empty (cap : ℕ) (m : Memory w) (steps : List (Online.Run.Step A.size A.size w))
    (run : Online.Run.Interval A.plan pt cap m steps)
    (empty : ∀ st ∈ steps, ∀ r ∈ st.row.reports, choiceBits r.events = []) :
    ∀ st ∈ steps, st.row.choices = List.replicate st.row.choices.length [] := by
  induction steps generalizing m with
  | nil => simp
  | cons st rest ih =>
    intro u hu
    rcases List.mem_cons.mp hu with rfl|hu
    · have paths := ((runSegment_iff ..).mp run.1.source.sourceRun).2.2
      apply List.eq_replicate_length.mpr
      intro b hb
      rw [← paths] at hb
      obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hb
      exact empty _ List.mem_cons_self r hr
    · exact ih _ run.2 (fun u mem ↦ empty u (List.mem_cons_of_mem _ mem)) u hu

theorem quiet (L : Layout) (a b l width cap : ℕ) (m : Memory w) (steps : List (Online.Run.Step A.size A.size w))
    (run : Online.Run.Interval A.plan pt cap m steps)
    (trace : (steps.map (fun st ↦ st.row.reports)).flatten = BlockInitialPackets.logs L a b l width m) :
    Online.Run.intervalBits steps = List.replicate (Online.Run.intervalBits steps).length [] := by
  apply Online.Run.quietInterval
  apply bits_empty A pub cap m steps run
  intro st hs r hr
  apply BlockInitialPackets.quiet L a b l width m r
  rw [← trace]
  exact List.mem_flatten.mpr ⟨st.row.reports,List.mem_map.mpr ⟨st,hs,rfl⟩,hr⟩

/-- Each accepting framed tape has the entire verified prefix, also when
the next selected level admits no accepting branches. -/
def cut (L : Layout) (a b l width cap : ℕ) (m : Memory w) (steps : List (Online.Run.Step A.size A.size w))
    (bounds : Online.Run.ControlBounds A.plan cap (w := w)) (tagged : m (pt).tag.val = tag)
    (bank : Workspace.Installed (arity A.catalog) (pub 2) m)
    (run : Online.Run.Interval A.plan pt cap m steps)
    (stable : SourceBankFrame.Stable ((pub 2).val+6) m (Online.Run.intervalLog A.plan pt m steps))
    (trace : (steps.map (fun st ↦ st.row.reports)).flatten = BlockInitialPackets.logs L a b l width m) :
    Cut P (cap+24) (some 0) m Unit :=
  let inner := Online.Run.intervalSegment A.plan pt (state := 0) bounds tagged steps run
  let outer := OnlineWorkspace.framedSegment A.plan pub inner (stable.banks bank)
  Cut.deterministic outer (Online.Run.intervalBits steps).length (quiet A pub L a b l width cap m steps run trace)

private theorem valid_at_end (cap : ℕ) (m : Memory w) (steps : List (Online.Run.Step A.size A.size w))
    (run : Online.Run.Interval A.plan pt cap m steps)
    (closed : let endMem := Online.Run.finalMemory (C := A.catalog) pt m steps
      endMem (pt).rows.val ≤ endMem (pt).ordinal.val) :
    Online.Run.Valid A.plan pt cap m steps := by
  induction steps generalizing m with
  | nil => exact closed
  | cons s rest ih => exact ⟨run.1,ih _ run.2 closed⟩

private theorem logs_end (m : Memory w) (steps : List (Online.Run.Step A.size A.size w)) :
    Online.Run.reports A.plan pt m steps = Online.Run.intervalLog A.plan pt m steps ++
      [Online.linked pt (Online.calendarIndex A.size A.size)
        (LevelCalendar.closedReport (pt).data (Online.Run.finalMemory (C := A.catalog) pt m steps))] := by
  induction steps generalizing m with
  | nil => rfl
  | cons s ss ih =>
    simp only [Online.Run.reports,Online.Run.intervalLog,Online.Run.finalMemory,ih,List.append_assoc]

/-- When the four initial rows exhaust the calendar, the fully framed
program has exactly one accepting tape and one report log. -/
theorem exhausted (L : Layout) (a b l width cap : ℕ) (m : Memory w) (steps : List (Online.Run.Step A.size A.size w))
    (bounds : Online.Run.ControlBounds A.plan cap (w := w)) (tagged : m (pt).tag.val = tag)
    (bank : Workspace.Installed (arity A.catalog) (pub 2) m)
    (run : Online.Run.Interval A.plan pt cap m steps)
    (stable : SourceBankFrame.Stable ((pub 2).val+6) m (Online.Run.intervalLog A.plan pt m steps))
    (trace : (steps.map (fun st ↦ st.row.reports)).flatten = BlockInitialPackets.logs L a b l width m)
    (closed : let endMem := Online.Run.finalMemory (C := A.catalog) pt m steps
      endMem (pt).rows.val ≤ endMem (pt).ordinal.val) :
    let bs := Online.Run.choices steps
    let logs := OnlineWorkspace.framed (pub 2) m (Online.Run.reports A.plan pt m steps)
    runSegment P (cap+24) (some 0) m bs = some logs ∧ endState (some 0) logs = none ∧
      ∀ other rs, runSegment P (cap+24) (some 0) m other = some rs → endState (some 0) rs = none →
        other = bs ∧ rs = logs := by
  intro bs logs
  have hv := valid_at_end A pub cap m steps run closed
  have native := Online.Run.execute A.plan pt steps m 0 cap tagged bounds.tags bounds.calendar bounds.launch hv
  have yes := (Online.Run.effect A.plan pt steps m 0 hv).2
  have full : SourceBankFrame.Stable ((pub 2).val+6) m (Online.Run.reports A.plan pt m steps) := by
    rw [logs_end A pub m steps]
    apply stable.append
    have endMemory := Online.Run.interval_memory A.plan pt (state := 0) bounds tagged steps run
    change after m (eventLog (Online.Run.intervalLog A.plan pt m steps)) = _ at endMemory
    rw [endMemory]
    refine ⟨?_,trivial⟩
    intro x _
    exact congrFun (Online.terminal_effect (initial := A.initial.length) (phases := A.block.length)
      (d := A.size) pt _).2.1 x
  have framed := OnlineWorkspace.run_framed A.plan pub cap (some 0) m bs _ native (full.banks bank)
  have halt : endState (some 0) logs = none := (OnlineWorkspace.framed_effect (pub 2) m _ (some 0)).1.trans yes
  have empty : bs = List.replicate bs.length [] := by
    have q := quiet A pub L a b l width cap m steps run trace
    change Online.Run.intervalBits steps ++ [[]] = List.replicate (Online.Run.intervalBits steps ++ [[]]).length []
    rw [List.length_append,List.replicate_add,← q]
    rfl
  refine ⟨framed,halt,?_⟩
  intro other rs otherRun otherHalt
  obtain ⟨unique,exactLogs⟩ := accepted_empty_unique (empty ▸ framed) halt otherRun otherHalt
  exact ⟨unique.trans empty.symm,exactLogs⟩

end CompressorRecords.InitialConverse

end VPVNP
end Computability
end OAI

import OAI.Computability.VPVNP.PairSimulationTerminalCall
import OAI.Computability.VPVNP.CompressorSourceTransport
import OAI.Computability.VPVNP.PrimedScheduleRAM

/-!
# Splicing ordinary worker stages into the terminal table

A closed stage can be run from a physical memory that differs from its source
memory on the two terminal control cells. Source reads avoid those cells.
Worker writes propagate to both memories, and the terminal controller updates
the stage and saved word between calls. The final accepting call either starts
the next worker at zero or halts the terminal table.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalLink

open BurstRAM LiveProgram CompressorRecords

variable {w : ℕ}

/-- An external address outside the two terminal-controller cells. -/
def workerCell (addr : Word w) (i : ℕ) : Prop := i ≠ addr.val ∧ i ≠ (addr+31).val

/-- Entry state selected by the final accepting call of a worker. -/
def handoff (s : Stage) : Option (Entry w) := (next s).map (fun t => .resume t 0)

/-- Attach each call's entry and exit events, restoring the cursor returned
by the preceding call. A closed source stage has one accepting call at its end. -/
def stageReports (addr : Word w) : Entry w → List (Report w) → List (Report w)
  | _, [] => []
  | e, raw :: more => report addr e raw :: stageReports addr (.resume e.stage (raw.result.getD 0)) more

@[simp] theorem length_stageReports (addr : Word w) (e : Entry w) (raws : List (Report w)) :
    (stageReports addr e raws).length = raws.length := by
  induction raws generalizing e <;> simp_all [stageReports]

private theorem after_cons (m : Memory w) (raw : Report w) (rs : List (Report w)) :
    after m (eventLog (raw::rs)) = after (after m raw.events) (eventLog rs) := List.foldl_append

private theorem report_agree (addr : Word w) (e : Entry w) (raw : Report w) (src phy : Memory w)
    (agree : SourceTransport.Agree (workerCell addr) src phy) :
    SourceTransport.Agree (workerCell addr) (after src raw.events) (after phy (report addr e raw).events) := by
  rw [report_after]
  cases ht : target e.stage raw.result with
  | none => exact agree.after _
  | some sv =>
    obtain ⟨s,v⟩ := sv
    intro i hi
    simpa [writeMemory,hi.1,hi.2] using agree.after raw.events i hi

variable (workers : Stage → PairTable) (pub : Fin 11 → Word w)

/-- The native reports, persistent handoff and the memory conditions needed to
splice the next stage at the end of this particular closed stage. -/
structure StageRun (cap : ℕ) (e : Entry w) (src phy : Memory w) (bs : List (List Bool)) (raws : List (Report w)) : Prop where
  run : runSegment (program workers pub) cap (some e.marker) phy bs =
    some (stageReports (header pub) e raws)
  state : endState (some e.marker) (stageReports (header pub) e raws) = (handoff e.stage).map Entry.marker
  agree : SourceTransport.Agree (workerCell (header pub)) (after src (eventLog raws))
    (after phy (eventLog (stageReports (header pub) e raws)))
  valid : ∀ t, handoff e.stage = some t → t.Valid (header pub) (after phy (eventLog (stageReports (header pub) e raws)))

/-- Replay the worker's own choices in the terminal machine. Correctness of
each source read is transported through memory agreement before executing that
call, and agreement is re-established after its physical exit. -/
theorem closed_stage_run (f cap : ℕ) (e : Entry w) (src phy : Memory w) (bs : List (List Bool))
    (raws : List (Report w)) (fit : 32 ≤ 2^w) (room : f+30 ≤ cap) (valid : e.Valid (header pub) phy)
    (agree : SourceTransport.Agree (workerCell (header pub)) src phy)
    (reads : SourceTransport.Reads (workerCell (header pub)) (eventLog raws))
    (run : runSegment (source workers e.stage pub) f (some e.state) src bs = some raws)
    (halt : endState (some e.state) raws = none) :
    StageRun workers pub cap e src phy bs raws := by
  induction bs generalizing e src phy raws with
  | nil =>
    have he : raws = [] := by simpa [runSegment] using run.symm
    simp [he,endState] at halt
  | cons b bs ih =>
    cases hraw : execute (source workers e.stage pub) f ((source workers e.stage pub).start e.state) src b with
    | none => simp [runSegment,hraw] at run
    | some raw =>
      simp only [runSegment,hraw,Option.map_eq_some_iff] at run
      obtain ⟨rs,tail,rfl⟩ := run
      have readHead : SourceTransport.Reads (workerCell (header pub)) raw.events :=
        fun a v h => reads a v (List.mem_append_left (eventLog rs) h)
      have readTail : SourceTransport.Reads (workerCell (header pub)) (eventLog rs) :=
        fun a v h => reads a v (List.mem_append_right raw.events h)
      obtain ⟨guessed,correct,bits⟩ := execute_spec hraw
      have physical : execute (source workers e.stage pub) f ((source workers e.stage pub).start e.state) phy b =
          some raw := execute_iff.mpr ⟨guessed,SourceTransport.correct agree readHead correct,bits⟩
      have linkedRun := call_of_room workers pub cap e phy b (by omega) valid f raw physical room
      have cells := report_agree (header pub) e raw src phy agree
      change endState raw.result rs = none at halt
      cases hx : raw.result with
      | none =>
        rw [hx] at tail
        cases bs with
        | cons b bs => simp [runSegment] at tail
        | nil =>
          have hrs : rs = [] := by simpa [runSegment] using tail.symm
          subst rs
          have hnext : e.follow raw = handoff e.stage := by
            simp [Entry.follow,handoff,target,hx,Option.map_map,Function.comp_def]
          constructor
          · simp [runSegment,linkedRun,stageReports]
          · simp [stageReports,endState,report_result,hnext]
          · simpa [stageReports,eventLog,after] using cells
          · intro t ht
            have hvalid := next_valid (header pub) e t raw phy fit (hnext.trans ht)
            simpa [stageReports,eventLog,after] using hvalid
      | some v =>
        let e' : Entry w := .resume e.stage v
        have follows : e.follow raw = some e' := by simp [Entry.follow,target,hx,e']
        have live := next_valid (header pub) e e' raw phy fit follows
        have endWord : (report (header pub) e raw).result = some e'.marker := by rw [report_result,follows]; rfl
        rw [hx] at tail halt
        have rest := ih (e := e') (src := after src raw.events) (phy := after phy (report (header pub) e raw).events)
          (raws := rs) live cells readTail tail halt
        constructor
        · simp only [runSegment,linkedRun,endWord,rest.run,stageReports,hx,Option.getD_some,Option.map_some,e']
        · simpa only [stageReports,hx,Option.getD_some,endState,endWord,e',Entry.stage] using rest.state
        · simpa only [stageReports,hx,Option.getD_some,after_cons] using rest.agree
        · simpa only [stageReports,hx,Option.getD_some,after_cons,e',Entry.stage] using rest.valid

/-- Continuing a linked execution consumes the stage's entire branch prefix
and resumes from its exact physical memory and marker. -/
theorem StageRun.append {workers : Stage → PairTable} {pub : Fin 11 → Word w} {cap : ℕ} {e : Entry w}
    {src phy : Memory w} {bs : List (List Bool)} {raws : List (Report w)}
    (h : StageRun workers pub cap e src phy bs raws) (tail : List (List Bool)) :
    let L := program workers pub
    let out := stageReports (header pub) e raws
    runSegment L cap (some e.marker) phy (bs++tail) =
      (runSegment L cap ((handoff e.stage).map Entry.marker) (after phy (eventLog out)) tail).map (out++·) := by
  dsimp only
  rw [PrimedSchedule.runSegment_append,h.run,Option.bind_some,h.state]

end PairSimulation.TerminalLink

end VPVNP
end Computability
end OAI

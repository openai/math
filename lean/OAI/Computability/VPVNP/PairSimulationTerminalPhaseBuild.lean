import OAI.Computability.VPVNP.PairSimulationTerminalDeterministic

/-!
# Constructing the five terminal phases from native worker runs

Pair each original report with its genuine entry state and use the read
footprint to execute the worker on the physical memory. At an ordinary
return the next entry uses the returned word, including when that word is
zero. At acceptance the phase ends at the actual memory after the handoff.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalLink

open BurstRAM LiveProgram CompressorRecords

variable {w : ℕ}

/-- The worker's report list annotated with the state at each call. -/
def stageLogs : Entry w → List (Report w) → List (Log w)
  | _, [] => []
  | e, raw :: rs => (e,raw) :: stageLogs (.resume e.stage (raw.result.getD 0)) rs

@[simp] theorem stageLogs_raw (e : Entry w) (raws : List (Report w)) :
    (stageLogs e raws).map Prod.snd = raws := by
  induction raws generalizing e <;> simp_all [stageLogs]

theorem reports_stageLogs (addr : Word w) (e : Entry w) (raws : List (Report w)) :
    reports addr (stageLogs e raws) = stageReports addr e raws := by
  induction raws generalizing e <;> simp_all [stageLogs,reports,stageReports]

theorem stageLogs_eq {workers : Stage → PairTable} {pub : Fin 11 → Word w}
    {cap e m bs ls final} (h : Phase workers pub cap e m bs ls final) :
    ls = stageLogs e (ls.map Prod.snd) := by
  induction h with
  | last => rfl
  | more _ _ returned _ ih =>
    simp only [List.map_cons,stageLogs,returned,Option.getD_some]
    rw [← ih]

variable (workers : Stage → PairTable) (pub : Fin 11 → Word w)

/-- A closed one-call phase executes on exactly the given physical memory,
including any reads or writes of the controller cells inside the worker. -/
theorem single_phase (f cap : ℕ) (e : Entry w) (m : Memory w) (bs : List Bool) (raw : Report w)
    (room : f+30 ≤ cap)
    (run : execute (source workers e.stage pub) f ((source workers e.stage pub).start e.state) m bs = some raw)
    (halt : raw.result = none) :
    Phase workers pub cap e m [bs] [(e,raw)] (after m (report (header pub) e raw).events) := by
  have pre := prefix_length_le (header pub) e
  have len := report_length_le (header pub) e raw
  change ((e.prefixEvents (header pub)) ++ (exitReport (header pub) e.stage raw).events).length ≤ _ at len
  rw [List.length_append] at len
  have small := (execute_spec run).1.length_lt
  have hf : f ≤ rawFuel pub cap e := by unfold rawFuel; omega
  exact .last (Nat.add_sub_of_le hf ▸ execute_extend run (rawFuel pub cap e-f))
    (by unfold rawFuel; omega) halt

theorem initial_phase (f cap : ℕ) (m : Memory w) (raw : Report w) (room : f+30 ≤ cap)
    (run : execute (source workers Stage.bootstrap pub) f ((source workers Stage.bootstrap pub).start 0) m [] = some raw)
    (halt : raw.result = none) :
    Phase workers pub cap .initial m [[]] [(.initial,raw)] (after m (report (header pub) .initial raw).events) :=
  single_phase workers pub f cap .initial m [] raw room run halt

/-- Build an actual completed phase from the ordinary worker's finite
execution. The caller may place arbitrary values in both control cells. -/
theorem closed_phase (f cap : ℕ) (e : Entry w) (src phy : Memory w) (bs : List (List Bool))
    (raws : List (Report w)) (room : f+30 ≤ cap)
    (agree : SourceTransport.Agree (workerCell (header pub)) src phy)
    (reads : SourceTransport.Reads (workerCell (header pub)) (eventLog raws))
    (run : runSegment (source workers e.stage pub) f (some e.state) src bs = some raws)
    (halt : endState (some e.state) raws = none) :
    Phase workers pub cap e phy bs (stageLogs e raws) (after phy (eventLog (stageReports (header pub) e raws))) := by
  induction bs generalizing e src phy raws with
  | nil =>
    have h : raws = [] := by simpa [runSegment] using run.symm
    simp [h,endState] at halt
  | cons b bs ih =>
    cases hc : execute (source workers e.stage pub) f ((source workers e.stage pub).start e.state) src b with
    | none => simp [runSegment,hc] at run
    | some raw =>
      simp only [runSegment,hc,Option.map_eq_some_iff] at run
      obtain ⟨rs,tail,rfl⟩ := run
      have readHead : SourceTransport.Reads (workerCell (header pub)) raw.events :=
        fun a v h => reads a v (List.mem_append_left (eventLog rs) h)
      have readTail : SourceTransport.Reads (workerCell (header pub)) (eventLog rs) :=
        fun a v h => reads a v (List.mem_append_right raw.events h)
      obtain ⟨path,correct,bits⟩ := execute_spec hc
      have hp : execute _ f _ phy b = some raw :=
        execute_iff.mpr ⟨path,SourceTransport.correct agree readHead correct,bits⟩
      have pre := prefix_length_le (header pub) e
      have length := report_length_le (header pub) e raw
      change ((e.prefixEvents (header pub)) ++ (exitReport (header pub) e.stage raw).events).length ≤ _ at length
      rw [List.length_append] at length
      have small := path.length_lt
      have fuel : f ≤ rawFuel pub cap e := by unfold rawFuel; omega
      have fits : (exitReport (header pub) e.stage raw).events.length < rawFuel pub cap e := by unfold rawFuel; omega
      have full := Nat.add_sub_of_le fuel ▸ execute_extend hp (rawFuel pub cap e-f)
      change endState raw.result rs = none at halt
      cases hr : raw.result with
      | none =>
        rw [hr] at tail
        cases bs with
        | cons b bs => simp [runSegment] at tail
        | nil =>
          obtain rfl := Option.some.inj tail
          simpa [stageLogs,stageReports,eventLog,after] using Phase.last full fits hr
      | some x =>
        rw [hr] at tail halt
        have frame : SourceTransport.Agree (workerCell (header pub)) (after src raw.events)
            (after phy (report (header pub) e raw).events) := by
          rw [report_after]
          simp only [target,hr]
          intro i hi
          simpa only [writeMemory,ite_eq_right hi.1,ite_eq_right hi.2] using agree.after raw.events i hi
        have rest := ih (.resume e.stage x) (after src raw.events) _ rs frame readTail tail halt
        have appended := Phase.more full fits hr rest
        simpa only [stageLogs,stageReports,hr,Option.getD_some,eventLog,List.flatMap_cons,after,List.foldl_append]
          using appended

/-- Implicit-parameter form for constructing a phase in a larger traversal. -/
theorem Phase.of_source_segment {workers : Stage → PairTable} {pub : Fin 11 → Word w}
    {f cap : ℕ} {e : Entry w} {src phy : Memory w} {bs : List (List Bool)} {rs : List (Report w)}
    (room : f+30 ≤ cap) (agree : SourceTransport.Agree (workerCell (header pub)) src phy)
    (reads : SourceTransport.Reads (workerCell (header pub)) (eventLog rs))
    (run : runSegment (source workers e.stage pub) f (some e.state) src bs = some rs)
    (halt : endState (some e.state) rs = none) :
    Phase workers pub cap e phy bs (stageLogs e rs) (after phy (eventLog (stageReports (header pub) e rs))) :=
  closed_phase workers pub f cap e src phy bs rs room agree reads run halt

end PairSimulation.TerminalLink

end VPVNP
end Computability
end OAI

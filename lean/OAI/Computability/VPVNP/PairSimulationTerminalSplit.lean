import OAI.Computability.VPVNP.PairSimulationTerminalVisits
import OAI.Computability.VPVNP.PairSimulationTerminalSplice

/-!
# Recovering each terminal stage from an accepted native traversal

Split at the first accepting exit of the currently selected worker.
A worker return stays within the same stage with its exact returned word.
The split preserves the remaining DFS calls, their memory and their bit
strings. Away from the two controller cells the recovered worker can be
replayed as an ordinary RAM segment.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalLink

open BurstRAM PrivateRAM LiveProgram CompressorRecords
open scoped Fin.CommRing

variable {w : ℕ} (workers : Stage → PairTable) (pub : Fin 11 → Word w) (cap : ℕ)

/-- All calls of one worker up to and including its accepting exit. -/
inductive Phase : Entry w → Memory w → List (List Bool) → List (Log w) → Memory w → Prop
  | last {e m bs raw}
      (call : execute (source workers e.stage pub) (rawFuel pub cap e)
        ((source workers e.stage pub).start e.state) m bs = some raw)
      (room : (exitReport (header pub) e.stage raw).events.length < rawFuel pub cap e)
      (accepted : raw.result = none) :
      Phase e m [bs] [(e,raw)] (after m (report (header pub) e raw).events)
  | more {e m b bs raw x ls final}
      (call : execute (source workers e.stage pub) (rawFuel pub cap e)
        ((source workers e.stage pub).start e.state) m b = some raw)
      (room : (exitReport (header pub) e.stage raw).events.length < rawFuel pub cap e)
      (returned : raw.result = some x)
      (tail : Phase (.resume e.stage x) (after m (report (header pub) e raw).events) bs ls final) :
      Phase e m (b::bs) ((e,raw)::ls) final

private theorem follow_halt (e : Entry w) (raw : Report w) (h : raw.result = none) :
    e.follow raw = handoff e.stage := by cases hn : next e.stage <;> simp [Entry.follow,target,h,handoff,hn]

private theorem follow_return (e : Entry w) (raw : Report w) {x : Word w} (h : raw.result = some x) :
    e.follow raw = some (.resume e.stage x) := by simp [Entry.follow,target,h]

theorem split_stage (e : Entry w) (m : Memory w) (bs : List (List Bool)) (ls : List (Log w))
    (visits : Visits workers pub cap (some e) m bs ls) (closed : finish (some e) ls = none) :
    ∃ first more rs rest final, bs = first++more ∧ ls = rs++rest ∧
      Phase workers pub cap e m first rs final ∧ Visits workers pub cap (handoff e.stage) final more rest ∧
      finish (handoff e.stage) rest = none := by
  induction bs generalizing e m ls with
  | nil => cases visits; contradiction
  | cons b bs ih =>
    cases visits with
    | @cons _ _ _ _ raw tail hc room later =>
      change finish (e.follow raw) tail = none at closed
      cases h : raw.result with
      | none =>
        rw [follow_halt e raw h] at later closed
        exact ⟨[b],bs,[(e,raw)],tail,_,rfl,rfl,.last hc room h,later,closed⟩
      | some x =>
        rw [follow_return e raw h] at later closed
        obtain ⟨first,more,rs,rest,final, hb,hl,ph,remaining,last⟩ :=
          ih (.resume e.stage x) _ tail later closed
        exact ⟨b::first,more,(e,raw)::rs,rest,final,by rw [hb]; rfl,by rw [hl]; rfl,
          .more hc room h ph,remaining,last⟩

private theorem transfer_call {C : Type*} {P : BurstRAM.Program w C} {f : ℕ} {c : C} {m m' : Memory w}
    {bs : List Bool} {raw : Report w} {data : ℕ → Prop}
    (run : execute P f c m bs = some raw) (agree : SourceTransport.Agree data m m')
    (reads : SourceTransport.Reads data raw.events) : execute P f c m' bs = some raw := by
  obtain ⟨path,correct,choices⟩ := execute_spec run
  exact execute_iff.mpr ⟨path,SourceTransport.correct agree reads correct,choices⟩

private theorem agree_report (addr : Word w) (e : Entry w) (raw : Report w) (src phy : Memory w)
    (agree : SourceTransport.Agree (workerCell addr) src phy) :
    SourceTransport.Agree (workerCell addr) (after src raw.events) (after phy (report addr e raw).events) := by
  intro i hi
  rw [report_after]
  cases ht : target e.stage raw.result with
  | none => exact agree.after raw.events i hi
  | some x =>
    cases x
    simpa only [writeMemory,ite_eq_right hi.2,ite_eq_right hi.1] using agree.after raw.events i hi

/-- Recover the completed original worker, with every header transfer
removed from its output memory and every genuine branch string retained. -/
theorem Phase.source_segment {e m bs ls final} (ph : Phase workers pub cap e m bs ls final)
    (src : Memory w) (agree : SourceTransport.Agree (workerCell (header pub)) src m)
    (reads : SourceTransport.Reads (workerCell (header pub)) (eventLog (ls.map Prod.snd))) :
    runSegment (source workers e.stage pub) cap (some e.state) src bs = some (ls.map Prod.snd) ∧
      endState (some e.state) (ls.map Prod.snd) = none ∧
      SourceTransport.Agree (workerCell (header pub)) (after src (eventLog (ls.map Prod.snd))) final := by
  induction ph generalizing src with
  | @last e m b raw run _ accepted =>
    have rr : SourceTransport.Reads (workerCell (header pub)) raw.events := by simpa [eventLog] using reads
    have rawRun := transfer_call run (fun i hi => (agree i hi).symm) rr
    have hle : rawFuel pub cap e ≤ cap := Nat.sub_le ..
    have full : execute _ cap _ src b = some raw :=
      Nat.add_sub_of_le hle ▸ execute_extend rawRun (cap-rawFuel pub cap e)
    exact ⟨by simp [runSegment,full],by simp [endState,accepted],
      by simpa [eventLog] using agree_report (header pub) e raw src m agree⟩
  | @more e m b bs raw x ls final run _ returned tail ih =>
    change SourceTransport.Reads _ (raw.events++eventLog (ls.map Prod.snd)) at reads
    have headRead : SourceTransport.Reads _ raw.events := fun a v h => reads a v (List.mem_append_left _ h)
    have tailRead : SourceTransport.Reads _ (eventLog (ls.map Prod.snd)) := fun a v h => reads a v (List.mem_append_right _ h)
    have hr := transfer_call run (fun i hi => (agree i hi).symm) headRead
    have hle : rawFuel pub cap e ≤ cap := Nat.sub_le ..
    have full : execute _ cap _ src b = some raw :=
      Nat.add_sub_of_le hle ▸ execute_extend hr (cap-rawFuel pub cap e)
    obtain ⟨hs,hend,ha⟩ := ih (after src raw.events) (agree_report (header pub) e raw src m agree) tailRead
    change runSegment (source workers e.stage pub) cap (some x) _ _ = _ at hs
    refine ⟨by simp [runSegment,full,returned,hs],by simpa [endState,returned,Entry.state] using hend,?_⟩
    simpa only [List.map_cons,eventLog,List.flatMap_cons,after,List.foldl_append] using ha

end PairSimulation.TerminalLink

end VPVNP
end Computability
end OAI

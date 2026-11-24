import OAI.Computability.VPVNP.PairSimulationTerminalFive
import OAI.Computability.VPVNP.LiveHeaderProtectedCore

/-!
# Recovering deterministic terminal stages on arbitrary accepting tapes

For a known ordinary worker segment with only empty choice strings, transport
its reads into the actual memory before comparing each physical call. This
proves the actual segment has the same report, choices and final worker memory
even when its caller supplies an arbitrary candidate tape.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalLink

open BurstRAM PrivateRAM LiveProgram CompressorRecords
open scoped Fin.CommRing

variable {w : ℕ} {workers : Stage → PairTable} {pub : Fin 11 → Word w} {cap : ℕ}

theorem Phase.reports_eq {e m bs ls final} (h : Phase workers pub cap e m bs ls final) :
    reports (header pub) ls = stageReports (header pub) e (ls.map Prod.snd) := by
  induction h with
  | last => rfl
  | more _ _ returned _ ih => simp [reports,stageReports,returned] at ih ⊢; exact ih

theorem Phase.final_memory {e m bs ls final} (h : Phase workers pub cap e m bs ls final) :
    after m (eventLog (reports (header pub) ls)) = final := by
  induction h with
  | last => simp [eventLog,reports]
  | more _ _ _ _ ih =>
    simpa only [eventLog,reports,List.map_cons,List.flatMap_cons,after,List.foldl_append] using ih

private theorem after_agree (addr : Word w) (e : Entry w) (raw : Report w) (src phy : Memory w)
    (h : SourceTransport.Agree (workerCell addr) src phy) :
    SourceTransport.Agree (workerCell addr) (after src raw.events) (after phy (report addr e raw).events) := by
  rw [report_after]
  cases ht : target e.stage raw.result with
  | none => exact h.after _
  | some sv =>
    obtain ⟨t,x⟩ := sv
    intro i hi
    simpa only [writeMemory,ite_eq_right hi.1,ite_eq_right hi.2] using h.after raw.events i hi

private theorem force_head {C : Type*} {P : BurstRAM.Program w C} {f g : ℕ} {c : C} {phy src : Memory w}
    {bits : List Bool} {raw known : Report w} {data : ℕ → Prop}
    (call : execute P g c phy bits = some raw) (expected : execute P f c src [] = some known)
    (agree : SourceTransport.Agree data src phy) (reads : SourceTransport.Reads data known.events) :
    bits = [] ∧ raw = known := by
  obtain ⟨path,ok,choices⟩ := execute_spec expected
  have replay : execute P f c phy [] = some known :=
    execute_iff.mpr ⟨path,SourceTransport.correct agree reads ok,choices⟩
  exact execute_empty_forces_anyFuel replay call

/-- The witness needs a read bound only for the supplied deterministic
reference reports. The arbitrary candidate is taken directly from the
complete native path, with no hypothesis on its read addresses. -/
theorem Phase.force_empty {e phy bs ls final} (h : Phase workers pub cap e phy bs ls final)
    (src : Memory w) (n f : ℕ) (known : List (Report w))
    (expected : runSegment (source workers e.stage pub) f (some e.state) src (List.replicate n []) = some known)
    (halt : endState (some e.state) known = none)
    (agree : SourceTransport.Agree (workerCell (header pub)) src phy)
    (reads : SourceTransport.Reads (workerCell (header pub)) (eventLog known)) :
    bs = List.replicate n [] ∧ ls.map Prod.snd = known ∧
      SourceTransport.Agree (workerCell (header pub)) (after src (eventLog known)) final := by
  induction h generalizing n src known with
  | @last e phy b raw call room closed =>
    cases n with
    | zero =>
      have hk : known = [] := by simpa [runSegment] using expected.symm
      simp [hk,endState] at halt
    | succ n =>
      cases hc : execute (source workers e.stage pub) f ((source workers e.stage pub).start e.state) src [] with
      | none => simp [List.replicate_succ,runSegment,hc] at expected
      | some head =>
        simp only [List.replicate_succ,runSegment,hc,Option.map_eq_some_iff] at expected
        obtain ⟨tail,rest,rfl⟩ := expected
        have readHead : SourceTransport.Reads _ head.events := fun a v hv =>
          reads a v (List.mem_append_left (eventLog tail) hv)
        obtain ⟨rfl,rfl⟩ := force_head call hc agree readHead
        rw [closed] at rest
        cases n with
        | zero =>
          have ht : tail = [] := (Option.some.inj rest).symm
          subst tail
          exact ⟨rfl,rfl,by simpa [eventLog] using after_agree (header pub) e raw src phy agree⟩
        | succ n => simp [List.replicate_succ,runSegment] at rest
  | @more e phy b more raw x ls final call room returned next ih =>
    cases n with
    | zero =>
      have hk : known = [] := by simpa [runSegment] using expected.symm
      simp [hk,endState] at halt
    | succ n =>
      cases hc : execute (source workers e.stage pub) f ((source workers e.stage pub).start e.state) src [] with
      | none => simp [List.replicate_succ,runSegment,hc] at expected
      | some head =>
        simp only [List.replicate_succ,runSegment,hc,Option.map_eq_some_iff] at expected
        obtain ⟨tail,rest,rfl⟩ := expected
        have readHead : SourceTransport.Reads _ head.events := fun a v hv =>
          reads a v (List.mem_append_left (eventLog tail) hv)
        have readTail : SourceTransport.Reads _ (eventLog tail) := fun a v hv =>
          reads a v (List.mem_append_right head.events hv)
        obtain ⟨rfl,rfl⟩ := force_head call hc agree readHead
        rw [returned] at rest
        change endState raw.result tail = none at halt
        rw [returned] at halt
        obtain ⟨ht,hr,ha⟩ := ih (after src raw.events) n tail rest halt (after_agree (header pub) e raw src phy agree) readTail
        exact ⟨by simp [List.replicate_succ,ht],by simp [hr],
          by simpa only [eventLog,List.flatMap_cons,after,List.foldl_append] using ha⟩

/-- Every completed phase from the same physical entry agrees with a
completed phase that consumed only empty choice strings. -/
theorem Phase.force_quiet {e phy qs ls out qs' ls' out'}
    (known : Phase workers pub cap e phy qs ls out) (quiet : ∀ b ∈ qs, b = [])
    (candidate : Phase workers pub cap e phy qs' ls' out') :
    qs' = qs ∧ ls' = ls ∧ out' = out := by
  induction known generalizing qs' ls' out' with
  | @last e phy b raw call room closed =>
    have empty := quiet b (by simp)
    subst b
    cases candidate with
    | last act _ _ =>
      obtain ⟨rfl,rfl⟩ := execute_empty_forces_anyFuel call act
      exact ⟨rfl,rfl,rfl⟩
    | more act _ returned _ =>
      obtain ⟨rfl,rfl⟩ := execute_empty_forces_anyFuel call act
      simp [closed] at returned
  | @more e phy b bs raw x ls out call room returned later ih =>
    have empty := quiet b (by simp)
    subst b
    cases candidate with
    | last act _ closed =>
      obtain ⟨rfl,rfl⟩ := execute_empty_forces_anyFuel call act
      simp [closed] at returned
    | more act _ ret tail =>
      obtain ⟨rfl,rfl⟩ := execute_empty_forces_anyFuel call act
      rw [returned] at ret
      obtain rfl := Option.some.inj ret
      obtain ⟨rfl,rfl,rfl⟩ := ih (fun s hs => quiet s (List.mem_cons_of_mem _ hs)) tail
      exact ⟨rfl,rfl,rfl⟩

end PairSimulation.TerminalLink

end VPVNP
end Computability
end OAI

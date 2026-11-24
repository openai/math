import OAI.Computability.VPVNP.LiveEvaluatorRAMSchedule
import OAI.Computability.VPVNP.PrimedCounterCallPaths

/-!
# Native reports of scheduled live evaluator calls

A scheduled call starts with zeroed registers and private memory, executes
the fixed evaluator body, then compares the successor cursor with the call
count. The comparison contributes one final tick to the report. The two
footer instructions fit in a uniform allowance independent of the tape
radius and word width.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveEvaluatorRAM.Schedule

open BurstRAM BurstRAM.PrivateRAM PrimedInputRAM PrimedStackRAM
open UniversalMachine (Program)
open LiveEvaluatorRAMPrepare (prepare)

variable {w : ℕ}

/-- The concrete finite program specialized only by the word width and its four public words. -/
abbrev nativeProgram (p : UniversalMachine.Program) (pub : Pub → Word w) :=
  ((program p).instantiate w pub).program

/-- Enough fuel for every route through the acyclic body and both footer opcodes. -/
def callFuel (p : UniversalMachine.Program) : ℕ := (body (prepare p)).length + 2

/-- The terminal cursor comparison at the end of an actual call. -/
def nextState (pub : Pub → Word w) (st : Word w) : Option (Word w) :=
  if st + 1 = Fin.ofNat (2^w) (calls (pub 0).val) then none else some (st+1)

/-- The allocated cursor sequence halts on its last call, even when the total
number of calls is exactly the word modulus. -/
theorem nextState_at (pub : Pub → Word w) (i : ℕ) (hi : i < calls (pub 0).val)
    (hfit : calls (pub 0).val ≤ 2^w) :
    nextState pub (Fin.ofNat (2^w) i) =
      if i+1 = calls (pub 0).val then none else some (Fin.ofNat (2^w) (i+1)) := by
  have hadd : Fin.ofNat (2^w) i + 1 = Fin.ofNat (2^w) (i+1) :=
    Fin.ext (Nat.add_mod ..).symm
  rw [nextState, hadd]
  by_cases hl : i+1 = calls (pub 0).val
  · simp [hl]
  · have hsmall : i+1 < 2^w := by omega
    have hne : Fin.ofNat (2^w) (i+1) ≠ Fin.ofNat (2^w) (calls (pub 0).val) := by
      intro he
      have hv := congrArg Fin.val he
      change (i+1) % (2^w) = (calls (pub 0).val) % (2^w) at hv
      rw [Nat.mod_eq_of_lt hsmall] at hv
      rcases hfit.lt_or_eq with hs | hs
      · exact hl (hv.trans (Nat.mod_eq_of_lt hs))
      · rw [hs, Nat.mod_self] at hv; omega
    rw [ite_eq_right hne, ite_eq_right hl]

/-- Exact native success at the reset entry point. Report replay obtains precisely
the external memory produced by the body; the footer consumes no choice bit. -/
theorem nativeStep_iff (p : UniversalMachine.Program) (pub : Pub → Word w) (st : Word w)
    (m : Memory w) (bs : List Bool) (r : Report w) :
    execute (nativeProgram p pub) (callFuel p) ((nativeProgram p pub).start st) m bs = some r ↔
      ∃ es out m', Flow.Exec pub st (body (prepare p)) (fun _ => 0) m es out m' ∧
        choiceBits es = bs ∧ r.events = es ++ [.tick] ∧
        r.result = nextState pub st ∧ after m r.events = m' := by
  rw [show execute (nativeProgram p pub) (callFuel p) ((nativeProgram p pub).start st) m bs = some r ↔ _
    from PrimedCounter.Call.execute_iff (body (prepare p)) 29 30 pub st (fun _ => 0)
      (fun _ => 0) m bs (callFuel p) r]
  constructor
  · rintro ⟨es,out,m',he,-,hb,ht,hr,hm⟩
    obtain ⟨hn,hT⟩ := body_cursor he
    exact ⟨es,out,m',he,hb,ht,by simpa only [nextState,hn,hT] using hr,hm⟩
  · rintro ⟨es,out,m',he,hb,ht,hr,hm⟩
    obtain ⟨hn,hT⟩ := body_cursor he
    exact ⟨es,out,m',he,Nat.add_le_add_right (program_bound p he) 2,hb,ht,by simpa [nextState,hn,hT] using hr,hm⟩

/-- Compute the actual report from a successful scheduled body execution. -/
theorem nativeStep_of_exec {p : UniversalMachine.Program} {pub : Pub → Word w} {st : Word w}
    {m es out m'} (he : Flow.Exec pub st (body (prepare p)) (fun _ => 0) m es out m') :
    execute (nativeProgram p pub) (callFuel p) ((nativeProgram p pub).start st) m (choiceBits es) =
      some ⟨es ++ [.tick],nextState pub st⟩ := by
  refine (nativeStep_iff p pub st m _ _).mpr ⟨es,out,m',he,rfl,rfl,rfl,?_⟩
  change after m (es ++ [.tick]) = m'
  simpa [after, update] using PrimedCounter.Call.exec_memory he

/-- Existential report form for composing calls on a specified post-call memory. -/
theorem nativeStep_exists_iff (p : UniversalMachine.Program) (pub : Pub → Word w) (st : Word w)
    (m : Memory w) (bs : List Bool) (m' : Memory w) :
    (∃ r, execute (nativeProgram p pub) (callFuel p) ((nativeProgram p pub).start st) m bs = some r ∧
      after m r.events = m') ↔
    ∃ es out, Flow.Exec pub st (body (prepare p)) (fun _ => 0) m es out m' ∧ choiceBits es = bs := by
  constructor
  · rintro ⟨r,hr,hm⟩
    obtain ⟨es,out,mem,he,hb,-,-,hrm⟩ := (nativeStep_iff p pub st m bs r).mp hr
    exact ⟨es,out,hrm.symm.trans hm ▸ he,hb⟩
  · rintro ⟨es,out,he,rfl⟩
    refine ⟨_, nativeStep_of_exec he, ?_⟩
    change after m (es ++ [.tick]) = m'
    simpa [after, update] using PrimedCounter.Call.exec_memory he

/-- Every actual cell call leaves external memory intact, has an empty branch stream,
and makes exactly six external reads. -/
theorem nativeCell_report (p : UniversalMachine.Program) (pub : Pub → Word w) (st : Word w)
    (m : Memory w) (bs : List Bool) (r : Report w) (hs : st ≠ 0)
    (he : execute (nativeProgram p pub) (callFuel p) ((nativeProgram p pub).start st) m bs = some r) :
    bs = [] ∧ after m r.events = m ∧ r.probes = 6 ∧ r.result = nextState pub st := by
  obtain ⟨es,out,m',hex,hbits,hr,hn,hm⟩ := (nativeStep_iff p pub st m bs r).mp he
  obtain ⟨hmem,hb,hp⟩ := cell_call_cost hex hs
  refine ⟨hbits.symm.trans hb,hm.trans hmem,?_,hn⟩
  simp [Report.probes, hr, PrimedStackRAM.probes_append, hp, countProbes]


/-- Native cost of the cursor-zero call. Its initial source-state read is the
only extra probe beyond preparing the five scratch words. -/
theorem nativePrepare_report (p : UniversalMachine.Program) (pub : Pub → Word w)
    (m : Memory w) (bs : List Bool) (r : Report w) (hw : 2 ≤ w) (hcap : p.extra+2 ≤ 2^w)
    (he : execute (nativeProgram p pub) (callFuel p) ((nativeProgram p pub).start 0) m bs = some r) :
    r.probes = (if m (pub 1).val = 1 then 7 else 9) ∧ bs.length ≤ 1 := by
  obtain ⟨es,rs,m',hb,hbits,-,-,-⟩ := (nativeStep_iff p pub 0 m bs r).mp he
  obtain ⟨ep,rp,hprep,hbs⟩ := (initial_choices_iff p pub (fun _ => 0) m m' bs).mp
    ⟨es,rs,hb,hbits⟩
  let pre := loaded pub 0 (fun _ => 0) m
  have hcost := LiveEvaluatorRAMPrepare.prepare_cost p pub 0 pre m hw hcap rfl rfl hprep
  change countProbes ep = (if m (pub 1).val = 1 then 6 else 8) ∧ _ at hcost
  have hrun : Flow.Exec pub 0 (body (prepare p)) (fun _ => 0) m
      ((List.replicate 11 .tick ++ [.read (pub 1) (m (pub 1).val)]) ++
        (.tick :: ep) ++ List.replicate 8 .tick) (finished pub 0 rp) m' := by
    simpa only [body, List.append_assoc, List.cons_append] using
      (Flow.Exec.seq (load_exec pub 0 (fun _ => 0) m)
        (Flow.Exec.seq (Flow.Exec.ifEqYes (a := prepare p) (b := .seq locate cell) (l := 26) (q := 0) rfl
          hprep) (finish_exec pub 0 rp m')))
  have hh := nativeStep_of_exec hrun
  simp only [Flow.choiceBits_append, List.replicate_succ, List.replicate_zero,
    choiceBits, List.nil_append, List.append_nil, hbs] at hh
  have hr := congrArg Report.events (Option.some.inj (he.symm.trans hh))
  refine ⟨?_,hbs ▸ hcost.2.1⟩
  by_cases h : m (pub 1).val = 1 <;>
    simp [Report.probes, hr, PrimedStackRAM.probes_append,
      countProbes, hcost.1, h]

/-- Every returned report uses less than the fixed allowance, including its final tick. -/
theorem nativeStep_report_length (p : UniversalMachine.Program) (pub : Pub → Word w) (st : Word w)
    (m : Memory w) (bs : List Bool) (r : Report w)
    (he : execute (nativeProgram p pub) (callFuel p) ((nativeProgram p pub).start st) m bs = some r) :
    r.events.length < callFuel p := by
  obtain ⟨es,rs,m',hb,-,hev,-,-⟩ := (nativeStep_iff p pub st m bs r).mp he
  have hl := program_bound p hb
  simp [hev, callFuel]; omega

end LiveEvaluatorRAM.Schedule

end VPVNP
end Computability
end OAI

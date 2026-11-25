import OAI.Optimization.LinearProgramming.Geometry.MarkedRun
import OAI.Optimization.LinearProgramming.Recovery.OracleSteps

/-! Inline a finite scalar-oracle RAM program as ordinary RAM. Data operations use the
odd caller bank, all jumps are relocated, and every oracle opcode executes a real finite
handler in place. Every saved native state and every bit of the returned caller packet
are preserved in the stated memory relation. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace OracleInline

open RAM RAM.Callable Contract
open _root_.OAI.Optimization.LinearProgramming.Geometry.OracleSegments

variable {K : Type}

/-- A terminal source instruction returns to the shared continuation. The source's
actual success/restart tag is separately certified by the geometric status header. -/
def placed (source : OracleProgram) (h : Handler) (base : ℕ) (native : Memory K) (s : State K) : State K :=
  (Odd.memory native s.memory).atPC (if s.output.isSome then base+(fragment source h).size else entry source h base s.pc)

@[simp] theorem placed_live (source : OracleProgram) (h : Handler) (base : ℕ) (native m : Memory K) (pc : ℕ) :
    placed source h base native (m.atPC pc)=(Odd.memory native m).atPC (entry source h base pc) := rfl

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The callback contract permits a different post-service native memory while fixing
its exact relation to the augmented history. It requires only actual marked preconditions. -/
def Handles (f : Handler) (mark : QueryMark K) (o : ScalarOracle K) (P : K→Prop)
    (live : History K→Memory K→Prop) (bound : ℕ) : Prop :=
  ∀ (s e : Memory K) (history : History K) (src len dst count : ℕ), s.AllData P → e.AllData P →
    live history e → mark s src len dst count →
    let q:=sentPacket s src len
    let a:=o history q
    ∃ e', e'.AllData P ∧ live ((q,a)::history) e' ∧
      (f src len dst count).Run P (Odd.memory e s) bound (Odd.memory e' (received s dst count a))

/-- One physical prefix inside every enclosing ordinary program and at every relocation. -/
def Between (source : OracleProgram) (f : Handler) (P : K→Prop)
    (e s : Memory K × State K) (bound : ℕ) : Prop :=
  ∀ (p : Program) (base : ℕ), CodeAt p base ((fragment source f).emit base) →
    ∃ n ≤ bound, Execution p (fun st=>∀ j,P (st.data j)) (placed source f base e.1 e.2) n (placed source f base s.1 s.2)

private theorem scalar_execution {p : Program} {P : K→Prop} {a t : State K} {k : ℕ}
    (run : Execution p (fun s => s.memory.AllData P) a k t) :
    Execution p (fun s => ∀ j, P (s.data j)) a k t := by
  have policy : (fun s : State K => s.memory.AllData P) = (fun s => ∀ j, P (s.data j)) := rfl
  exact Eq.mp (congrArg (fun Q : State K→Prop => Execution p Q a k t) policy) run

private theorem branch_run (P : K→Prop) (target : Program) (m native : Memory K) (safe : m.AllData P) (sn : native.AllData P)
    (source : OracleProgram) (f : Handler) (base pc yes no : ℕ) (c : Cond) (t : State K)
    (op : execInstr (c.instr yes no) (m.atPC pc)=some t)
    (code : CodeAt target (entry source f base pc) [(Odd.cond c).instr (entry source f base yes) (entry source f base no)]) :
    Execution target (fun st=>∀ j,P (st.data j)) ((Odd.memory native m).atPC (entry source f base pc)) 1
      (placed source f base native t) := by
  have eq := Option.some.inj ((cond_exec c m pc yes no).symm.trans op)
  subst t
  have test := scalar_execution (P:=P) (Block.Eval.test_exec (safe:=Memory.AllData P) target (Odd.cond c) (Odd.memory native m)
    (entry source f base pc) (entry source f base yes) (entry source f base no) (Odd.allData native m sn safe) code.head)
  rw [Odd.cond_test] at test
  cases h : c.test m <;> simpa only [h,Bool.false_eq_true,ite_true,ite_false,placed_live] using test

private theorem core_run (P : K→Prop) (source : OracleProgram) (f : Handler) (m native : Memory K) (t : State K)
    (pc : ℕ) (op : Instr) (fetch : source[pc]?=some (.core op)) (edge : execInstr op (m.atPC pc)=some t)
    (sm : m.AllData P) (st : t.memory.AllData P) (sn : native.AllData P) :
    Between source f P (native,m.atPC pc) (native,t) 4 := by
  intro target base code
  have ci:=at_core code fetch
  by_cases plain : fallsThrough op=true
  · obtain ⟨state,eval⟩:=ordinary_eval plain edge P sm st
    have halt : t.output=none := congrArg State.output state
    have pos : t.pc=pc+1 := congrArg State.pc state
    rw [coreCode_fallsThrough op plain] at ci
    have eq : entry source f base (pc+1)=entry source f base pc+(Odd.instr op).size := by
      simpa only [width,coreWidth_fallsThrough op plain] using (entry_succ (handler:=f) (base:=base) fetch)
    refine ⟨Odd.instrCost op,Odd.instrCost_le op,?_⟩
    change Execution target _ (placed source f base native (m.atPC pc)) _ (placed source f base native t)
    rw [placed_live]
    simpa only [placed,halt,Option.isSome_none,Bool.false_eq_true,ite_false,pos,eq] using
      scalar_execution (P:=P) ((Odd.instr_eval P native sn op eval).compile_correct ci)
  · cases op with
    | jump q =>
      have eq : m.atPC q=t := Option.some.inj edge
      subst t
      exact ⟨1,by decide,Block.Eval.jump_exec (safe:=Memory.AllData P) target _ _ _ (Odd.allData native m sn sm) ci.head⟩
    | halt tag =>
      have eq : ({m.atPC pc with output:=some tag} : State K)=t := Option.some.inj edge
      subst t
      rw [entry_end] at ci
      exact ⟨1,by decide,Block.Eval.jump_exec (safe:=Memory.AllData P) target _ _ _ (Odd.allData native m sn sm) ci.head⟩
    | branchLT a b yes no => exact ⟨1,by decide,branch_run P target m native sm sn source f base pc yes no (.scalarLT a b) t edge ci⟩
    | branchAddrLT a b yes no => exact ⟨1,by decide,branch_run P target m native sm sn source f base pc yes no (.addrLT a b) t edge ci⟩
    | _ => contradiction

private theorem single {source : OracleProgram} {f : Handler} {mark : QueryMark K} {o : ScalarOracle K}
    {P : K→Prop} {live : History K→Memory K→Prop} {bound : ℕ} (handle : Handles f mark o P live bound)
    {s t : Config K} {n : ℕ} (checked : CheckedEdge mark source s) (edge : oracleStep source o s=some (n,t))
    (sm : s.state.memory.AllData P) (st : t.state.memory.AllData P) (e : Memory K) (se : e.AllData P) (h : live s.history e) :
    ∃ e',e'.AllData P ∧ live t.history e' ∧ Between source f P (e,s.state) (e',t.state) (n*(max 4 bound)) := by
  obtain ⟨active,op,fetch⟩:=step_fetch edge
  cases op with
  | core i =>
    obtain ⟨one,history,act⟩:=step_core fetch edge
    have actual:=core_run P source f s.state.memory e t.state s.state.pc i fetch (by simpa only [live_memory active] using act) sm st se
    refine ⟨e,se,history.symm ▸ h,?_⟩
    intro prog pc code
    obtain ⟨k,hk,run⟩:=actual prog pc code
    exact ⟨k,by rw [one,one_mul];exact hk.trans (le_max_left _ _),by simpa only [live_memory active] using run⟩
  | query src len dst count =>
    obtain ⟨cost,tlive,pos,mem,hist⟩:=step_query fetch edge
    obtain ⟨e',safe,store,go⟩:=handle _ e s.history src len dst count sm se h (checked _ _ _ _ fetch)
    refine ⟨e',safe,hist.symm ▸ store,?_⟩
    intro prog base code
    obtain ⟨k,hk,run⟩:=go prog (entry source f base s.state.pc) (at_query code fetch)
    have succ:=entry_succ (handler:=f) (base:=base) fetch
    have paid : 0 < n := by omega
    refine ⟨k,hk.trans ((le_max_right _ _).trans (Nat.le_mul_of_pos_left _ paid)),?_⟩
    simpa only [placed,active,tlive,Option.isSome_none,Bool.false_eq_true,ite_false,pos,mem,succ,width] using run

/-- The per-source-step compiler bound and the all-state height property of every
actual callback compose along the *same marked execution* and original scalar history. -/
theorem marked_simulation {source : OracleProgram} {f : Handler} {mark : QueryMark K} {o : ScalarOracle K}
    {P : K→Prop} {Q : Memory K→Prop} {live : History K→Memory K→Prop} {bound : ℕ}
    (handle : Handles f mark o P live bound) (widthOK : ∀ m,Q m→m.AllData P)
    {s t : Config K} {n : ℕ} (run : MarkedRun mark source o Q s n t)
    (e : Memory K) (se : e.AllData P) (h : live s.history e) :
    ∃ e',e'.AllData P ∧ live t.history e' ∧ Between source f P (e,s.state) (e',t.state) (n*(max 4 bound)) := by
  induction run generalizing e with
  | refl c hs =>
    refine ⟨e,se,h,fun prog base _=>⟨0,by simp,.done _ ?_⟩⟩
    exact Odd.allData e c.state.memory se (widthOK _ hs)
  | next hs checked edge rest ih =>
    obtain ⟨e',se',h',first⟩:=single handle checked edge (widthOK _ hs) (widthOK _ rest.start) e se h
    obtain ⟨z,sz,hz,last⟩:=ih e' se' h'
    refine ⟨z,sz,hz,?_⟩
    intro prog base code
    obtain ⟨i,hi,a⟩:=first prog base code
    obtain ⟨j,hj,b⟩:=last prog base code
    exact ⟨i+j,by rw [Nat.add_mul];omega,a.append b⟩

/-- A complete finite oracle ROM becomes one explicit ordinary fragment. The result
contains the real service bank reached by the entire adaptive exchange sequence. -/
theorem fragment_runs {source : OracleProgram} {f : Handler} {mark : QueryMark K} {o : ScalarOracle K}
    {P : K→Prop} {Q : Memory K→Prop} {live : History K→Memory K→Prop} {bound : ℕ}
    (handle : Handles f mark o P live bound) (widthOK : ∀ m,Q m→m.AllData P)
    (m e : Memory K) (hist : History K) (se : e.AllData P) (he : live hist e)
    {n : ℕ} {last : Config K} (run : MarkedRun mark source o Q ⟨m.atPC 0,hist⟩ n last) (halt : last.state.output.isSome=true) :
    ∃ e',e'.AllData P ∧ live last.history e' ∧ (fragment source f).Run P (Odd.memory e m) (n*(max 4 bound)) (Odd.memory e' last.state.memory) := by
  obtain ⟨e',safe,ok,compiled⟩:=marked_simulation handle widthOK run e se he
  refine ⟨e',safe,ok,?_⟩
  intro prog base code
  obtain ⟨k,hk,exec⟩:=compiled prog base code
  change Execution prog _ (placed source f base e (m.atPC 0)) k (placed source f base e' last.state) at exec
  rw [placed_live,entry_start] at exec
  exact ⟨k,hk,by simpa only [placed,halt,ite_true] using exec⟩

end OracleInline
end Recovery
end LinearProgramming
end Optimization
end OAI

import OAI.Optimization.LinearProgramming.BitRAM.DispatchPrefix
import OAI.Optimization.LinearProgramming.BitRAM.DispatchCompiler

/-! The LP epoch driver may end immediately when its minor-compression service restarts.
This block returns before performing the next genuine price request. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace BitRAM
namespace Dispatch

variable {K : Type*}
open RAM RAM.Block RAM.Tape OracleSpec

def Stop.represented {p : BitProgram} (stop : Stop p) (m : Memory K) : Prop :=
  match stop with
  | .halted c => Rep p c m
  | .request c q => Awaiting p c q m

def afterIssue (p : BitProgram) : Block :=
  .branch (.addrLT nilReg askReg) (.op (.addrConst limitReg 0)) (.op (.addrConst limitReg p.states))

def untilLoop (p : BitProgram) : Block :=
  .loop (.addrLT stateReg limitReg) (.seq (issuedTable p) (afterIssue p))

/-- Actual ordinary instructions, with a sentinel local to this call. On an ordinary
step it is reset to the number of states. On a queued request it becomes zero. -/
def runUntilRequest (p : BitProgram) : Block :=
  .seq (.op (.addrConst limitReg p.states)) (untilLoop p)

private theorem issue_ordinary {p : BitProgram} {c t : p.Config} {op : Op p} {m : Memory K}
    (e : Issued p c op m) (h : ordinaryTarget c op = some t) : Rep p t m := by
  cases e with
  | ordinary next r => exact (Option.some.inj (next.symm.trans h)) ▸ r
  | ask _ => simp [ordinaryTarget] at h

private theorem issue_ask {p : BitProgram} {c : p.Config} {q : Fin p.states} {m : Memory K}
    (e : Issued p c (.ask q) m) : Awaiting p c q m := by
  cases e with
  | ordinary h _ => simp [ordinaryTarget] at h
  | ask r => exact r

private theorem wait_limit {p : BitProgram} {c : p.Config} {q : Fin p.states} {m : Memory K}
    (r : Awaiting p c q m) (v : ℕ) : Awaiting p c q (m.putIndex limitReg v) :=
  ⟨r.heap.putScratch (i := limitReg) (by decide) _,
    (Memory.putIndex_ne _ (by decide : bufferLenReg ≠ limitReg) _).trans r.bufferLength,
    (Memory.putIndex_ne _ (by decide : stateReg ≠ limitReg) _).trans r.stateCode,
    (Memory.putIndex_ne _ (by decide : askReg ≠ limitReg) _).trans r.askFlag⟩

private theorem header_refl (m : Memory K) : StableHeaders m m := fun _ _ _ => rfl

private theorem header_comp {a b c : Memory K} (ab : StableHeaders a b) (bc : StableHeaders b c) :
    StableHeaders a c := fun i lo hi => (bc i lo hi).trans (ab i lo hi)

private theorem header_limit (m : Memory K) (v : ℕ) : StableHeaders m (m.putIndex limitReg v) := by
  intro i lo _
  exact Memory.putIndex_ne _ (by unfold limitReg; omega) _

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Properties of the physical memory preserved over this table and the local
loop sentinel. Both the interface-header frame and the application-cache frame below
are proved by the concrete linked table. -/
structure PrefixFrame (p : BitProgram) (P : K → Prop) where
  rel : Memory K → Memory K → Prop
  refl : ∀ m, rel m m
  trans : ∀ {m a t}, rel m a → rel a t → rel m t
  limit : ∀ m v, rel m (m.putIndex limitReg v)
  table : ∀ {c : p.Config} {q : Fin p.states} {m : Memory K}, c.pc=some q → Rep p c m → Good P m →
    ∃ t k, k ≤ 2*p.states+27 ∧ Eval (Good P) (issuedTable p) m k t ∧
      Issued p c (p.instruction q (c.store (p.scan q)).head?) t ∧ t.data=m.data ∧ rel m t

def headerFrame (p : BitProgram) (P : K → Prop) : PrefixFrame p P where
  rel := StableHeaders
  refl := header_refl
  trans := header_comp
  limit := header_limit
  table := fun {c q m} pc r g => issuedTable_correct (p := p) (c := c) (q := q) (m := m) pc r g

private theorem untilLoop_correct {p : BitProgram} {c : p.Config} {n : ℕ} {stop : Stop p}
    {P : K → Prop} (frame : PrefixFrame p P) (pre : Prefix p c n stop) {m : Memory K}
    (rep : Rep p c m) (safe : Good P m) (limit : m.index limitReg=p.states) :
    ∃ t k, k ≤ (2*p.states+35)*(n+1)+1 ∧ Eval (Good P) (untilLoop p) m k t ∧
      stop.represented t ∧ t.data=m.data ∧ frame.rel m t := by
  induction pre generalizing m with
  | halted pc =>
    have test : (Cond.addrLT stateReg limitReg).test m = false := by
      simp [Cond.test,rep.stateCode,pcCode,pc,limit]
    exact ⟨m,1,by simp,Eval.loopFalse test safe,rep,rfl,frame.refl m⟩
  | @request c q next pc ask =>
    have test : (Cond.addrLT stateReg limitReg).test m = true := by
      simp [Cond.test,rep.stateCode,pcCode,pc,limit]
    obtain ⟨mid,j,hj,code,issue,hd,hf⟩ := frame.table pc rep safe
    rw [ask] at issue
    have wait := issue_ask issue
    have flagged : (Cond.addrLT nilReg askReg).test mid = true := by
      simp [Cond.test,wait.heap.nilValue,wait.askFlag]
    let t := mid.putIndex limitReg 0
    have done := wait_limit wait 0
    have set : Eval (Good P) (afterIssue p) mid (1+1+1) t :=
      Eval.branchTrue flagged (eval_constI mid code.safe_end limitReg 0)
    have finish : Eval (Good P) (untilLoop p) t 1 t := Eval.loopFalse (by simp [Cond.test,t]) set.safe_end
    refine ⟨t,1+(j+3)+1+1,?_,Eval.loopTrue test (code.seq set) finish,done,hd,frame.trans hf (frame.limit mid 0)⟩
    simp only [Nat.zero_add,Nat.mul_one]
    omega
  | @next c q midConfig n stop pc ord tail ih =>
    have test : (Cond.addrLT stateReg limitReg).test m = true := by
      simp [Cond.test,rep.stateCode,pcCode,pc,limit]
    obtain ⟨mid,j,hj,code,issue,hd,hf⟩ := frame.table pc rep safe
    have after := issue_ordinary issue ord
    have flagged : (Cond.addrLT nilReg askReg).test mid = false := by
      simp [Cond.test,after.heap.nilValue,after.askReady]
    let t := mid.putIndex limitReg p.states
    have prepared := after.putScratch (i := limitReg) (by decide) p.states
    have set : Eval (Good P) (afterIssue p) mid (1+1) t :=
      Eval.branchFalse flagged (eval_constI mid code.safe_end limitReg p.states)
    obtain ⟨out,k,hk,cont,last,data,tailFrame⟩ := ih prepared set.safe_end (by simp)
    refine ⟨out,1+(j+2)+1+k,?_,Eval.loopTrue test (code.seq set) cont,last,data.trans hd,
      frame.trans hf (frame.trans (frame.limit mid _) tailFrame)⟩
    rw [Nat.mul_succ]
    omega

/-- The ordinary block returns control before the next numeric service. It preserves every
scalar cell and each live external header throughout the interpreted prefix. -/
theorem runUntilRequest_with_frame {p : BitProgram} {c : p.Config} {n : ℕ} {stop : Stop p}
    {P : K → Prop} (frame : PrefixFrame p P) (pre : Prefix p c n stop) {m : Memory K} (rep : Rep p c m) (safe : Good P m) :
    ∃ t k, k ≤ (2*p.states+35)*(n+1)+2 ∧ Eval (Good P) (runUntilRequest p) m k t ∧
      stop.represented t ∧ t.data=m.data ∧ frame.rel m t := by
  have start := eval_constI m safe limitReg p.states
  obtain ⟨out,k,hk,run,done,data,tailFrame⟩ :=
    untilLoop_correct frame pre (rep.putScratch (i := limitReg) (by decide) p.states) start.safe_end (by simp)
  exact ⟨out,1+k,by omega,start.seq run,done,data,frame.trans (frame.limit m _) tailFrame⟩

theorem runUntilRequest_correct {p : BitProgram} {c : p.Config} {n : ℕ} {stop : Stop p}
    (pre : Prefix p c n stop) {P : K → Prop} {m : Memory K} (rep : Rep p c m) (safe : Good P m) :
    ∃ t k, k ≤ (2*p.states+35)*(n+1)+2 ∧ Eval (Good P) (runUntilRequest p) m k t ∧
      stop.represented t ∧ t.data=m.data ∧ StableHeaders m t :=
  by simpa only [headerFrame] using runUntilRequest_with_frame (headerFrame p P) pre rep safe

/-- Apply the ordinary program to a real halted source run. The suffix starts at precisely
the answered configuration if a request is queued, and reports the exact original time. -/
theorem runUntilRequest_of_run {p : BitProgram} {o : WordOracle} {c d : p.Config} {time : ℕ}
    (r : p.Run o c time d) (halted : d.pc=none)
    {P : K → Prop} {m : Memory K} (rep : Rep p c m) (safe : Good P m) :
    ∃ n stop t k, Prefix p c n stop ∧ Suffix o n time d stop ∧
      k ≤ (2*p.states+35)*(n+1)+2 ∧ Eval (Good P) (runUntilRequest p) m k t ∧
      stop.represented t ∧ t.data=m.data ∧ StableHeaders m t := by
  obtain ⟨n,stop,pre,post⟩ := prefix_of_run r halted
  obtain ⟨t,k,hk,ev,done,data,frame⟩ := runUntilRequest_correct pre rep safe
  exact ⟨n,stop,t,k,pre,post,hk,ev,done,data,frame⟩

end Dispatch
end BitRAM
end LinearProgramming
end Optimization
end OAI

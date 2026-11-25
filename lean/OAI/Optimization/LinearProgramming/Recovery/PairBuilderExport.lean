import OAI.Optimization.LinearProgramming.Recovery.PairBuilderWorkers

/-! Finite native rank/pointer receipts and dense exports, including caller frames. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace PairBuilder
open RAM RAM.Block RAM.Call RAM.Callable RAM.Tape Matrix
open _root_.OAI.Optimization.LinearProgramming.Geometry

variable {K : Type}
variable {h n k s a b : ℕ} {l : Layout h n}

noncomputable def exportCost {h n : ℕ} (l : Layout h n) := metaBudget.eval (limit l)+(21*(n*n)+7)

/-- Choose the final address of the first packed basis after receiving its actual rank. -/
theorem first_export [Field K] [LinearOrder K] [IsStrictOrderedRing K] (rev : Bool) (native caller : Memory K) (P : K→Prop) (v : Internal l k s a b caller)
    (hn : native.AllData P) (hc : caller.AllData P) (r : ℕ) (rank : native.index 165=r) (fit : r ≤ n) :
    ∃t,(firstExport rev).Run P (Odd.memory native caller) (exportCost l) (Odd.memory native t) ∧ t.AllData P ∧
      Internal l r s (firstDst rev l.out n r) (secondDst rev l.out n r) t ∧
      uniformRect r n (firstDst rev l.out n r) t=uniformRect r n (native.index 57) native ∧
      Copied caller t (firstDst rev l.out n r) (r*n) := by
  let x:=caller.putIndex 206 r
  let y:=x.putIndex 180 (native.index 57)
  have rx : (receive 165 206).Run P (Odd.memory native caller) 1 (Odd.memory native x) := by
    simpa only [receive, x, rank] using Fragment.Run.ofBlock (BankRead.receiveIndex_eval P native caller hn hc 165 206)
  have ry : (receive 57 180).Run P (Odd.memory native x) 1 (Odd.memory native y) :=
    Fragment.Run.ofBlock (BankRead.receiveIndex_eval P native x hn hc 57 180)
  have vy : Internal l r s a b y := (v.setFirst r fit).pointed _
  obtain ⟨z,rz,sz,q⟩:=vy.metaRun (.place rev) native P hn hc
  obtain ⟨vz,dst,num⟩:=place_values rev vy q
  have src : z.index 180=native.index 57 := (q.kept 180 (by cases rev <;> decide)).trans (by simp [y])
  have hi : 5 ≤ firstDst rev l.out n r := by have o:=l.minimum; have e:=l.sourceRoom; have f:=(first_range rev l r fit).1; omega
  obtain ⟨t,copy,st,vt,table,frame⟩:=copy_table native z P vz hn sz r _ _ src dst num hi
  have passive : Passive caller y := (Passive.index caller 206 r (by decide)).trans (Passive.index x 180 _ (by decide))
  have cells:=Nat.mul_le_mul_right n fit
  refine ⟨t,(rx.seq (ry.seq (rz.seq copy))).mono ?_,st,vt,table,(passive.trans q.passive).copied frame⟩
  unfold exportCost; omega

inductive OutPort where | residual | last

def OutPort.phase : OutPort→Phase | .residual=>.copyResidual | .last=>.copyLast
def OutPort.pointer : OutPort→ℕ | .residual=>58 | .last=>57
def OutPort.rows (port : OutPort) (n s : ℕ) := match port with | .residual=>n | .last=>s
def OutPort.destination (port : OutPort) (l : Layout h n) (last : ℕ) := match port with | .residual=>l.scratch | .last=>last

def simpleExport (port : OutPort) := (receive port.pointer 180).seq ((«meta» port.phase).seq copyRows)

/-- Export a known table using a logical pointer read from the native result bank. -/
theorem simple_export [Field K] [LinearOrder K] [IsStrictOrderedRing K] (port : OutPort) (native caller : Memory K) (P : K→Prop) (v : Internal l k s a b caller)
    (hn : native.AllData P) (hc : caller.AllData P) (hd : 5 ≤ port.destination l b) :
    ∃t,(simpleExport port).Run P (Odd.memory native caller) (metaBudget.eval (limit l)+(21*(n*n)+6)) (Odd.memory native t) ∧
      t.AllData P ∧ Internal l k s a b t ∧
      uniformRect (port.rows n s) n (port.destination l b) t=uniformRect (port.rows n s) n (native.index port.pointer) native ∧
      Copied caller t (port.destination l b) (port.rows n s*n) := by
  let x:=caller.putIndex 180 (native.index port.pointer)
  have rx : (receive port.pointer 180).Run P (Odd.memory native caller) 1 (Odd.memory native x) :=
    Fragment.Run.ofBlock (BankRead.receiveIndex_eval P native caller hn hc port.pointer 180)
  have vx : Internal l k s a b x := v.pointed _
  obtain ⟨y,ry,sy,q⟩:=vx.metaRun port.phase native P hn hc
  have quiet : Quiet port.phase := by cases port <;> trivial
  have src : y.index 180=native.index port.pointer := (q.kept 180 (by cases port <;> decide)).trans (by simp [x])
  have dst : y.index 181=port.destination l b := by
    cases port <;> simpa [OutPort.phase,OutPort.destination,plan,HeaderPlan.output,AddressTerm.value,vx.workspace,vx.lastBase] using q.updated 181
  have count : y.index 182=port.rows n s*n := by
    cases port <;> simpa [OutPort.phase,OutPort.rows,plan,HeaderPlan.output,AddressTerm.value,AddressOp.value,vx.width,vx.lastRank] using q.updated 182
  obtain ⟨t,copy,st,vt,table,frame⟩:=copy_table native y P (q.quiet quiet vx) hn sy _ _ _ src dst count hd
  have fit : port.rows n s ≤ n := by cases port <;> simp [OutPort.rows,v.lastFits]
  have cells:=Nat.mul_le_mul_right n fit
  refine ⟨t,(rx.seq (ry.seq copy)).mono ?_,st,vt,table,((Passive.index _ 180 _ (by decide)).trans q.passive).copied frame⟩
  omega

theorem last_export [Field K] [LinearOrder K] [IsStrictOrderedRing K] (native caller : Memory K) (P : K→Prop) (v : Internal l k s a b caller)
    (hn : native.AllData P) (hc : caller.AllData P) (r : ℕ) (rank : native.index 165=r) (fit : r ≤ n) (hd : 5 ≤ b) :
    ∃t,lastExport.Run P (Odd.memory native caller) (exportCost l) (Odd.memory native t) ∧ t.AllData P ∧ Internal l k r a b t ∧
      uniformRect r n b t=uniformRect r n (native.index 57) native ∧ Copied caller t b (r*n) := by
  let x:=caller.putIndex 207 r
  have rx : (receive 165 207).Run P (Odd.memory native caller) 1 (Odd.memory native x) := by
    simpa only [receive, x, rank] using Fragment.Run.ofBlock (BankRead.receiveIndex_eval P native caller hn hc 165 207)
  obtain ⟨t,run,safe,store,table,frame⟩:=simple_export .last native x P (v.setLast r fit) hn hc hd
  refine ⟨t,(rx.seq run).mono ?_,safe,store,table,(Passive.index _ 207 _ (by decide)).copied frame⟩
  unfold exportCost; omega

end PairBuilder
end Recovery
end LinearProgramming
end Optimization
end OAI

import OAI.Optimization.LinearProgramming.Geometry.OracleSegments
import OAI.Optimization.LinearProgramming.RAM.CallableOddLeaf
import OAI.Optimization.LinearProgramming.Recovery.OracleLayout

/-! Decompose a scalar-oracle machine step. A query determines the complete returned
memory and charges the request and response words. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace OracleInline

open RAM Contract
open _root_.OAI.Optimization.LinearProgramming.Geometry.OracleSegments

variable {K : Type}

theorem live_memory {s : State K} (h : s.output=none) : s.memory.atPC s.pc=s := by
  cases s; simp_all [State.memory,Memory.atPC]

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem step_fetch {p : OracleProgram} {o : ScalarOracle K} {s t : Config K} {cost : ℕ}
    (h : oracleStep p o s=some (cost,t)) : s.state.output=none ∧ ∃ i,p[s.state.pc]?=some i := by
  cases s with
  | mk m hist =>
    cases tag : m.output with
    | some z => simp [oracleStep,tag] at h
    | none =>
      cases op : p[m.pc]? with
      | none => simp [oracleStep,tag,op] at h
      | some i => exact ⟨rfl,i,rfl⟩

theorem step_core {p : OracleProgram} {o : ScalarOracle K} {s t : Config K} {cost : ℕ} {i : Instr}
    (fetch : p[s.state.pc]?=some (.core i)) (edge : oracleStep p o s=some (cost,t)) :
    cost=1 ∧ t.history=s.history ∧ execInstr i s.state=some t.state := by
  obtain ⟨live,_⟩:=step_fetch edge
  rcases s with ⟨s,h⟩
  rcases t with ⟨t,k⟩
  change p[s.pc]?=some (.core i) at fetch
  change s.output=none at live
  cases act : execInstr i s with
  | none => simp [oracleStep,live,fetch,act] at edge
  | some w =>
    have e : ((1,⟨w,h⟩):ℕ × Config K)=(cost,⟨t,k⟩) := by simpa [oracleStep,live,fetch,act] using edge
    cases e; exact ⟨rfl,rfl,rfl⟩

theorem step_query {p : OracleProgram} {o : ScalarOracle K} {s t : Config K} {cost src len dst count : ℕ}
    (fetch : p[s.state.pc]?=some (.query src len dst count)) (edge : oracleStep p o s=some (cost,t)) :
    let q:=sentPacket s.state.memory src len
    let a:=o s.history q
    cost=1+q.length+a.length ∧ t.state.output=none ∧ t.state.pc=s.state.pc+1 ∧
      t.state.memory=received s.state.memory dst count a ∧ t.history=(q,a)::s.history := by
  obtain ⟨live,_⟩:=step_fetch edge
  obtain ⟨s,h⟩:=s
  obtain ⟨t,k⟩:=t
  exact (by
    have real:=Contraction.Machine.query_exchange p o s h (by exact fetch) (by exact live)
    have same:=Option.some.inj (real.symm.trans edge)
    cases same
    exact ⟨rfl,by exact live,rfl,rfl,rfl⟩)

/-- An arithmetic or address opcode can be run at any relocated program counter.
The four genuine control operations are handled by the inliner's jump table. -/
theorem ordinary_eval {i : Instr} (ok : fallsThrough i=true) {m : Memory K} {pc : ℕ} {t : State K}
    (edge : execInstr i (m.atPC pc)=some t) (P : K→Prop) (sm : m.AllData P) (st : t.memory.AllData P) :
    t=t.memory.atPC (pc+1) ∧ Block.Eval (Memory.AllData P) (.op i) m 1 t.memory := by
  have changePC : t=t.memory.atPC (pc+1) ∧ ∀ j,execInstr i (m.atPC j)=some (t.memory.atPC (j+1)) := by
    cases i with
    | div d x y =>
      by_cases zero : m.data y=0
      · simp [execInstr,Memory.atPC,zero] at edge
      · have eq : (m.atPC pc).putData d (m.data x/m.data y)=t := by simpa [execInstr,Memory.atPC,zero] using edge
        subst t
        exact ⟨rfl,fun j=>by simp [execInstr,Memory.atPC,State.putData,State.memory,zero]⟩
    | _ =>
      first | exact (Bool.noConfusion ok) | (have eq:=Option.some.inj edge; subst t; exact ⟨rfl,fun _=>rfl⟩)
  exact ⟨changePC.1,.op sm st changePC.2⟩

theorem cond_exec (c : Cond) (m : Memory K) (pc yes no : ℕ) :
    execInstr (c.instr yes no) (m.atPC pc)=some (m.atPC (if c.test m then yes else no)) := by
  cases c with
  | scalarLT a b => by_cases h : m.data a < m.data b <;> simp [Cond.instr,Cond.test,Memory.atPC,execInstr,h]
  | addrLT a b => by_cases h : m.index a < m.index b <;> simp [Cond.instr,Cond.test,Memory.atPC,execInstr,h]

end OracleInline
end Recovery
end LinearProgramming
end Optimization
end OAI

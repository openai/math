import OAI.Optimization.LinearProgramming.BitRAM.NativePending
import OAI.Optimization.LinearProgramming.BitRAM.ReceiveReply
import OAI.Optimization.LinearProgramming.BitRAM.ServiceRaw

/-! A restart or defeat returns the numerical service's actual terminal state to the
outer LP epoch. A normal return decodes the full reply and resumes the pending bit machine. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace BitRAM
namespace NativeService
open RAM RAM.Block RAM.Tape RAM.Callable OracleSpec

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def replyOrInterrupt (p : BitProgram) (handler : Fragment) (statusReg : Nat) : Fragment :=
  .seq (.ofBlock preparePacket) (.seq handler (.branch (.addrLT nilReg statusReg)
    (.ofBlock .skip) (.ofBlock (receiveReply p))))

/-- A positive restart tag exits with precisely the raw service's terminal RAM, carrying
any persistent minor or numerical state described by `saved`. -/
theorem replyOrInterrupt_restart {p : BitProgram} {c : p.Config} {q : Fin p.states} {m : Memory K}
    {P : K→Prop} (pending : Awaiting p c q m) (safe : Good P m) (zero : P 0) (one : P 1)
    (send : 3 ≤ m.index sendBaseReg) (handler : Fragment) (statusReg budget : Nat) (saved : Memory K → Prop)
    (call : ∀ u, Awaiting p c q u → Good P u → PacketWriteEffect m u (m.index sendBaseReg) c.bufferRev →
      ScalarPacket u (u.index sendBaseReg) c.bufferRev.reverse →
      ∃ v, handler.Run P u budget v ∧ v.index nilReg<v.index statusReg ∧ saved v) :
    ∃ t, (replyOrInterrupt p handler statusReg).Run P m ((13*c.bufferRev.length+7)+(budget+2)) t ∧
      t.index nilReg<t.index statusReg ∧ saved t := by
  obtain ⟨u,prep,up,out,packet⟩ := prepare_awaiting pending safe zero one send
  obtain ⟨t,service,high,keep⟩ := call u up prep.safe_end out packet
  have test : (Cond.addrLT nilReg statusReg).test t=true := by simp [Cond.test,high]
  have pass := Fragment.Run.ofBlock (Block.Eval.skip (show Good P t from service.safe_end))
  exact ⟨t,(Fragment.Run.ofBlock prep).seq (service.seq (Fragment.Run.branchTrue test pass _)),high,keep⟩

/-- Status survives deserialization when it lives in an application header or a high
physical even cell. In particular, even-lifted geometric status uses register 278. -/
def StatusAddress (i : Nat) : Prop := (43 ≤ i ∧ i<65) ∨ (64 ≤ i ∧ i%2=0)

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
private theorem status_kept {p : BitProgram} {w : Slot p → Word} {v t : Memory K} {i : Nat}
    (heap : HeapRep p w v) (f : ReceiveReplyFrame p v t) (addr : StatusAddress i) : t.index i=v.index i := by
  have lower : 43 ≤ i := by rcases addr with h|h <;> omega
  apply f.index i _ (by unfold bufferReg; omega) (by unfold bufferLenReg; omega) (by unfold askReg; omega)
  rcases addr with ⟨hl,hu⟩|⟨hl,ev⟩
  · exact ReceiveKeep.header heap (some p.answerStack) (by omega) hu
  · have odd := (headReg_range p (some p.answerStack)).2.2
    exact ⟨by omega,by omega,by omega,by unfold freeReg; omega,by omega,Or.inr ev⟩

/-- A zero status decodes the returned bits, performs the exact frozen logical `ask`
transition, and keeps the normal status available to the outer scheduler. -/
theorem replyOrInterrupt_answer {p : BitProgram} {c : p.Config} {q : Fin p.states} {m : Memory K}
    {P : K→Prop} (pending : Awaiting p c q m) (safe : Good P m) (zero : P 0) (one : P 1)
    (send : 3 ≤ m.index sendBaseReg) (handler : Fragment) (statusReg budget : Nat) (addr : StatusAddress statusReg)
    (bits : Word) (saved : Memory K → Prop)
    (call : ∀ u, Awaiting p c q u → Good P u → PacketWriteEffect m u (m.index sendBaseReg) c.bufferRev →
      ScalarPacket u (u.index sendBaseReg) c.bufferRev.reverse → ∃ v,
        RawReply handler P u budget bits v ∧ v.index statusReg=0 ∧ 3 ≤ v.index recvBaseReg ∧ saved v) :
    ∃ v t, (replyOrInterrupt p handler statusReg).Run P m
      ((13*c.bufferRev.length+7)+(budget+(1+(18*bits.length+9)))) t ∧
      Rep p (receivedConfig p c q bits) t ∧ t.index statusReg=0 ∧ saved v ∧ ReceiveReplyFrame p v t := by
  obtain ⟨u,prep,up,out,pkt⟩ := prepare_awaiting pending safe zero one send
  obtain ⟨v,r,normal,recv,keep⟩ := call u up prep.safe_end out pkt
  have hv := r.heap up.heap
  have st : v.index stateReg=q.val := (r.frame _ (by decide) (by decide) (by decide) (by decide)).trans up.stateCode
  obtain ⟨t,read,rep,frame,_⟩ := receiveReply_rep_bits p c q bits hv r.run.safe_end zero st recv r.length r.packet
  have test : (Cond.addrLT nilReg statusReg).test v=false := by simp [Cond.test,normal]
  refine ⟨v,t,(Fragment.Run.ofBlock prep).seq (r.run.seq (Fragment.Run.branchFalse test _ (Fragment.Run.ofBlock read))),
    rep,(status_kept hv frame addr).trans normal,keep,frame⟩

end NativeService
end BitRAM
end LinearProgramming
end Optimization
end OAI

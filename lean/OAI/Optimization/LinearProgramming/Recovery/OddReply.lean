import OAI.Optimization.LinearProgramming.Recovery.OddBoundary

/-! A genuine physical price exchange returns the preserved numerical state on
interruption, and decodes only a successful reply. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace PackedPCG

open RAM RAM.Tape RAM.Callable OracleSpec BitRAM
variable {K : Type*}

private theorem safe_numeric {P : K→Prop} {a m : Memory K} (safe : (Odd.memory a m).AllData P) : a.AllData P :=
  fun j=>by simpa only [Odd.data_even] using safe (2*j)

private theorem safe_caller {P : K→Prop} {a m : Memory K} (safe : (Odd.memory a m).AllData P) : m.AllData P :=
  fun j=>by simpa only [Odd.data_slot] using safe (Odd.slot j)

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem transfer_restart {p : BitProgram} {c : p.Config} {q : Fin p.states} {m native : Memory K}
    {P : K→Prop} (pending : Awaiting p c q m) (safe : Good P m) (nativeSafe : native.AllData P)
    (zero : P 0) (one : P 1) (send : 3 ≤ m.index sendBaseReg) (handler : Fragment)
    (budget : ℕ) (keep : Memory K→Memory K→Prop)
    (call : ∀ u,Awaiting p c q u → Good P u → PacketWriteEffect m u (m.index sendBaseReg) c.bufferRev →
      ScalarPacket u (u.index sendBaseReg) c.bufferRev.reverse → ∃ a v,
      handler.Run P (Odd.memory native u) budget (Odd.memory a v) ∧
      v.index nilReg < v.index statusReg ∧ keep a v) :
    ∃ a t,(transfer p handler).Run P (Odd.memory native m) (4*(13*c.bufferRev.length+7)+budget+2)
      (Odd.memory a t) ∧ t.index nilReg < t.index statusReg ∧ keep a t := by
  obtain ⟨u,prep,up,out,pkt⟩:=prepare_awaiting pending safe zero one send
  obtain ⟨a,t,run,flag,stored⟩:=call u up prep.safe_end out pkt
  have guard : (Odd.cond (.addrLT nilReg statusReg)).test (Odd.memory a t)=true := by
    rw [Odd.cond_test]
    simp [Cond.test,flag]
  have pass:=Odd.leaf_run P a (safe_numeric run.safe_end) (Block.Eval.skip (safe_caller run.safe_end))
  refine ⟨a,t,((Odd.leaf_run P native nativeSafe prep).seq (run.seq (Fragment.Run.branchTrue guard pass _))).mono (by omega),flag,stored⟩

theorem transfer_answer {p : BitProgram} {c : p.Config} {q : Fin p.states} {m native : Memory K}
    {P : K→Prop} (pending : Awaiting p c q m) (safe : Good P m) (nativeSafe : native.AllData P)
    (zero : P 0) (one : P 1) (send : 3 ≤ m.index sendBaseReg) (handler : Fragment)
    (budget : ℕ) (bits : Word) (keep : Memory K→Memory K→Prop)
    (call : ∀ u,Awaiting p c q u → Good P u → PacketWriteEffect m u (m.index sendBaseReg) c.bufferRev →
      ScalarPacket u (u.index sendBaseReg) c.bufferRev.reverse → ∃ a v,
      handler.Run P (Odd.memory native u) budget (Odd.memory a v) ∧ HeapRep p (contents c) v ∧
      v.index stateReg=q.val ∧ v.index statusReg=0 ∧ 3 ≤ v.index recvBaseReg ∧
      v.index recvLenReg=bits.length ∧ ScalarPacket v (v.index recvBaseReg) bits ∧ keep a v) :
    ∃ a v t,(transfer p handler).Run P (Odd.memory native m)
      (4*(13*c.bufferRev.length+7)+budget+4*(18*bits.length+9)+2) (Odd.memory a t) ∧
      Rep p (receivedConfig p c q bits) t ∧ t.index statusReg=0 ∧ keep a v ∧ ReceiveReplyFrame p v t := by
  obtain ⟨u,prep,up,out,pkt⟩:=prepare_awaiting pending safe zero one send
  obtain ⟨a,v,run,heap,state,normal,recv,len,data,stored⟩:=call u up prep.safe_end out pkt
  obtain ⟨t,read,rep,frame,_⟩:=receiveReply_rep_bits p c q bits heap (safe_caller run.safe_end) zero state recv len data
  have guard : (Odd.cond (.addrLT nilReg statusReg)).test (Odd.memory a v)=false := by
    rw [Odd.cond_test]
    simp [Cond.test,normal]
  have rest:=(Odd.leaf_run P a (safe_numeric run.safe_end) read)
  have carry : t.index statusReg=v.index statusReg := by
    apply frame.index statusReg _ (by decide) (by decide) (by decide)
    exact ReceiveKeep.header heap (some p.answerStack) (by decide) (by decide)
  refine ⟨a,v,t,((Odd.leaf_run P native nativeSafe prep).seq (run.seq (Fragment.Run.branchFalse guard _ rest))).mono (by omega),
    rep,carry.trans normal,stored,frame⟩

end PackedPCG
end Recovery
end LinearProgramming
end Optimization
end OAI

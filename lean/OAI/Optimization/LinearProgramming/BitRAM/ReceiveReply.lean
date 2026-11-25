import OAI.Optimization.LinearProgramming.BitRAM.Receive

/-! The physical incoming-packet routine resumes the exact frozen bit machine after `ask`. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace BitRAM

variable {K : Type*}

open RAM RAM.Block RAM.Tape OracleSpec

def receivedConfig (p : BitProgram) (c : p.Config) (q : Fin p.states) (bits : Word) : p.Config :=
  {pc := some q,store := Function.update c.store p.answerStack bits,bufferRev := [],
    transcript := (c.bufferRev.reverse,bits)::c.transcript}

theorem contents_receivedConfig (p : BitProgram) (c : p.Config) (q : Fin p.states) (bits : Word) :
    contents (receivedConfig p c q bits)=answerWords p (contents c) bits := by
  funext s
  cases s with
  | none => simp [receivedConfig,contents,answerWords]
  | some s =>
    by_cases hs : s=p.answerStack
    · simp [hs,receivedConfig,contents,answerWords]
    · simp [receivedConfig,contents,answerWords,hs]

structure ReceiveReplyFrame (p : BitProgram) (m t : Memory K) : Prop where
  data (i : Nat) (h0 : i ≠ 0) (h2 : i ≠ 2) : t.data i=m.data i
  index (i : Nat) (keep : ReceiveKeep (some p.answerStack) m i)
    (hb : i ≠ bufferReg) (hl : i ≠ bufferLenReg) (ha : i ≠ askReg) : t.index i=m.index i
  headers (i : Nat) (low : 43 ≤ i) (high : i < 65) : t.index i=m.index i
  even (i : Nat) (low : 64 ≤ i) (parity : i%2=0) : t.index i=m.index i

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Recover the physical control invariant, including a cleared request flag, at the exact
post-`ask` configuration. The next instruction has already been selected at dispatch. -/
theorem receiveReply_rep_bits (p : BitProgram) (c : p.Config) (q : Fin p.states) (bits : Word)
    {P : K → Prop} {m : Memory K} (heap : HeapRep p (contents c) m) (safe : Good P m) (zero : P 0)
    (hstate : m.index stateReg=q.val) (hbase : 3 ≤ m.index recvBaseReg)
    (hlen : m.index recvLenReg=bits.length) (packet : ScalarPacket m (m.index recvBaseReg) bits) :
    ∃ t, Eval (Good P) (receiveReply p) m (18*bits.length+9) t ∧ Rep p (receivedConfig p c q bits) t ∧
      ReceiveReplyFrame p m t ∧ t.index freeReg=m.index freeReg+4*bits.length := by
  obtain ⟨a,first,heap',_,len,frame,free⟩ := loadAnswerChain_correct bits heap safe zero hbase hlen packet
  let t := a.putIndex askReg 0
  have last : Eval (Good P) (.op (.addrConst askReg 0)) a 1 t := Eval.op_addrConst a _ 0 first.safe_end first.safe_end
  have ht : HeapRep p (contents (receivedConfig p c q bits)) t := by
    rw [contents_receivedConfig]; exact heap'.putHeader (by decide) (by decide) 0
  have state := frame.index stateReg (ReceiveKeep.header heap _ (by decide) (by decide)) (by decide) (by decide)
  have keep (i : Nat) (hk : ReceiveKeep (some p.answerStack) m i)
      (hb : i≠bufferReg) (hl : i≠bufferLenReg) (ha : i≠askReg) : t.index i=m.index i :=
    (Memory.putIndex_ne a ha 0).trans (frame.index i hk hb hl)
  refine ⟨t,?_,⟨ht,?_,?_,by simp [t]⟩,?_,?_⟩
  · rw [show 18*bits.length+9 = (18*bits.length+8)+1 by omega]
    exact first.seq last
  · exact (Memory.putIndex_ne a (by decide : bufferLenReg ≠ askReg) 0).trans len
  · exact (Memory.putIndex_ne a (by decide : stateReg ≠ askReg) 0).trans (state.trans hstate)
  · refine ⟨frame.data,keep,?_,?_⟩
    · intro i low high
      exact keep i (ReceiveKeep.header heap _ (by omega) high) (by unfold bufferReg;omega)
        (by unfold bufferLenReg;omega) (by unfold askReg;omega)
    · intro i low parity
      have headOdd := (headReg_range p (some p.answerStack)).2.2
      have hk : ReceiveKeep (some p.answerStack) m i :=
        ⟨by omega,by omega,by omega,by unfold freeReg; omega,by omega,Or.inr parity⟩
      exact keep i hk (by unfold bufferReg;omega) (by unfold bufferLenReg;omega) (by unfold askReg;omega)
  · exact (Memory.putIndex_ne a (by decide : freeReg ≠ askReg) 0).trans free

/-- The physical result agrees with the exact transcript-dependent word oracle at the
frozen machine's `ask` boundary. -/
theorem receiveReply_rep (p : BitProgram) (c : p.Config) (q : Fin p.states) (oracle : WordOracle)
    {P : K → Prop} {m : Memory K} (heap : HeapRep p (contents c) m) (safe : Good P m) (zero : P 0)
    (hstate : m.index stateReg=q.val) (hbase : 3 ≤ m.index recvBaseReg)
    (hlen : m.index recvLenReg=(oracle c.transcript c.bufferRev.reverse).length)
    (packet : ScalarPacket m (m.index recvBaseReg) (oracle c.transcript c.bufferRev.reverse)) :
    let bits := oracle c.transcript c.bufferRev.reverse
    ∃ t, Eval (Good P) (receiveReply p) m (18*bits.length+9) t ∧ Rep p (receivedConfig p c q bits) t ∧
      ReceiveReplyFrame p m t ∧ t.index freeReg=m.index freeReg+4*bits.length :=
  receiveReply_rep_bits p c q _ heap safe zero hstate hbase hlen packet

end BitRAM
end LinearProgramming
end Optimization
end OAI

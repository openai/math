import OAI.Optimization.LinearProgramming.BitRAM.ReceiveLoop

/-! Fixed RAM conversion from an incoming scalar-bit packet to a linked binary stack. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace BitRAM

open RAM RAM.Block RAM.Tape OracleSpec

def loadChainFromScalars (p : BitProgram) (s : Slot p) : Block :=
  .seq (seekBlock recvBaseReg 12 10 recvLenReg) (.seq (.op (.addrConst (headReg s) 0))
    (.seq (.op (.const 0 0)) (receiveLoop s)))

def loadAnswerChain (p : BitProgram) : Block :=
  .seq (loadChainFromScalars p (some p.answerStack))
    (.seq (.op (.addrConst bufferReg 0)) (.op (.addrConst bufferLenReg 0)))

def receiveReply (p : BitProgram) : Block := .seq (loadAnswerChain p) (.op (.addrConst askReg 0))

@[simp] theorem loadChainFromScalars_size (p : BitProgram) (s : Slot p) : (loadChainFromScalars p s).size=31 := rfl

@[simp] theorem loadAnswerChain_size (p : BitProgram) : (loadAnswerChain p).size=33 := rfl

@[simp] theorem receiveReply_size (p : BitProgram) : (receiveReply p).size=34 := rfl

def answerWords (p : BitProgram) (w : Slot p → Word) (bits : Word) : Slot p → Word :=
  Function.update (Function.update w (some p.answerStack) bits) none []

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The selected chain is replaced irrespective of its old contents. The allocator advances
by four odd-layout address positions per bit and every earlier node remains immutable. -/
theorem loadChainFromScalars_correct {p : BitProgram} (s : Slot p) (bits : Word)
    {P : K → Prop} {w : Slot p → Word} {m : Memory K} (heap : HeapRep p w m) (safe : Good P m)
    (zero : P 0) (hbase : 3 ≤ m.index recvBaseReg) (hlen : m.index recvLenReg=bits.length)
    (packet : ScalarPacket m (m.index recvBaseReg) bits) :
    ∃ t, Eval (Good P) (loadChainFromScalars p s) m (18*bits.length+6) t ∧
      HeapRep p (Function.update w s bits) t ∧ ReceiveFrame s m t ∧
      t.index freeReg=m.index freeReg+4*bits.length := by
  obtain ⟨a,seek,ad,_,acur,aframe⟩ := seekBlock_correct P m recvBaseReg 12 10 recvLenReg bits.length
    (by decide) (by decide) (by decide) hlen safe
  have ah : HeapRep p w a := heap.of_odd_eq (fun j hj _ => aframe j (by omega) (by omega))
  let v := a.putIndex (headReg s) 0
  let z := v.putData 0 0
  have ev : Eval (Good P) (.op (.addrConst (headReg s) 0)) a 1 v := Eval.op_addrConst a _ 0 seek.safe_end seek.safe_end
  have vz : Good P z := fun i => by
    by_cases hi : i=0
    · simpa [z,hi] using zero
    · simpa [z,v,hi] using seek.safe_end i
  have ez : Eval (Good P) (.op (.const 0 0)) v 1 z := by
    simpa only [Rat.cast_zero] using Eval.op_const v 0 0 ev.safe_end (by simpa only [Rat.cast_zero] using vz)
  have zh : HeapRep p (Function.update w s []) z := (ah.clear_slot s).of_odd_eq (fun _ _ _ => rfl)
  have rn := headReg_range p s
  have nz : recvBaseReg ≠ headReg s := (ReceiveKeep.header heap s (i:=recvBaseReg) (by decide) (by decide)).2.2.2.2.1
  have zbase : z.index recvBaseReg=m.index recvBaseReg :=
    (Memory.putIndex_ne a nz 0).trans (aframe _ (by decide) (by decide))
  have zcur : z.index 12=m.index recvBaseReg+bits.length := (Memory.putIndex_ne a (by omega) 0).trans acur
  have zfree : z.index freeReg=m.index freeReg :=
    (Memory.putIndex_ne a (by unfold freeReg; omega) 0).trans (aframe _ (by decide) (by decide))
  have fr : ReceiveFrame s m z := by
    refine ⟨?_,?_⟩
    · intro i hi _
      simpa only [z,v,Memory.putData_ne _ hi, Memory.putIndex_data] using congrFun ad i
    · intro i hi
      exact (Memory.putIndex_ne a hi.2.2.2.2.1 0).trans (aframe i hi.2.1 hi.2.2.1)
  have pz : ScalarPacket z (m.index recvBaseReg) bits := packet.congr (fun i _ => fr.data _ (by omega) (by omega))
  obtain ⟨t,run,hfinal,output,free,_⟩ := receiveLoop_correct s bits _ hbase zh vz zbase zcur (by simp [z]) pz
  refine ⟨t,?_,?_,fr.trans output zfree.ge,by simpa only [zfree] using free⟩
  · have all := seek.seq (ev.seq (ez.seq run))
    rw [show 18*bits.length+6 = (4*bits.length+3)+(1+(1+(14*bits.length+1))) by omega]
    exact all
  · simpa only [Function.update_self,List.append_nil,Function.update_idem] using hfinal

/-- Frame after the answer chain is loaded and the submitted query buffer is cleared. -/
structure AnswerFrame (p : BitProgram) (m t : Memory K) : Prop where
  data (i : Nat) (h0 : i ≠ 0) (h2 : i ≠ 2) : t.data i=m.data i
  index (i : Nat) (keep : ReceiveKeep (some p.answerStack) m i) (hb : i ≠ bufferReg)
    (hl : i ≠ bufferLenReg) : t.index i=m.index i

theorem loadAnswerChain_correct {p : BitProgram} (bits : Word) {P : K → Prop} {w : Slot p → Word}
    {m : Memory K} (heap : HeapRep p w m) (safe : Good P m) (zero : P 0)
    (hbase : 3 ≤ m.index recvBaseReg) (hlen : m.index recvLenReg=bits.length)
    (packet : ScalarPacket m (m.index recvBaseReg) bits) :
    ∃ t, Eval (Good P) (loadAnswerChain p) m (18*bits.length+8) t ∧
      HeapRep p (answerWords p w bits) t ∧ t.index bufferReg=0 ∧ t.index bufferLenReg=0 ∧
      AnswerFrame p m t ∧ t.index freeReg=m.index freeReg+4*bits.length := by
  obtain ⟨a,run,heap',frame,free⟩ := loadChainFromScalars_correct (some p.answerStack) bits heap safe zero hbase hlen packet
  let b := a.putIndex bufferReg 0
  let t := b.putIndex bufferLenReg 0
  have eb : Eval (Good P) (.op (.addrConst bufferReg 0)) a 1 b := Eval.op_addrConst a _ 0 run.safe_end run.safe_end
  have et : Eval (Good P) (.op (.addrConst bufferLenReg 0)) b 1 t := Eval.op_addrConst b _ 0 eb.safe_end eb.safe_end
  have hb : HeapRep p (answerWords p w bits) b := heap'.clear_slot none
  refine ⟨t,?_,hb.putHeader (by decide) (by decide) 0,by simp [t,b,bufferLenReg,bufferReg],by simp [t],?_,?_⟩
  · rw [show 18*bits.length+8 = (18*bits.length+6)+(1+1) by omega]
    exact run.seq (eb.seq et)
  · refine ⟨frame.data,?_⟩
    intro i hk hb' hl
    simpa [t,b,hb',hl] using frame.index i hk
  · simpa [t,b,freeReg,bufferReg,bufferLenReg] using free

end BitRAM
end LinearProgramming
end Optimization
end OAI

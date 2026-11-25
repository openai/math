import OAI.Optimization.LinearProgramming.BitRAM.ReceiveBody

/-! The reply bits are scanned from right to left so the stack reads in their original order. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace BitRAM

open RAM RAM.Block RAM.Tape OracleSpec

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Reverse scan of a contiguous bit packet, prepending it to the selected linked word.
The scalar comparison constants and the packet itself survive all iterations. -/
theorem receiveLoop_correct {p : BitProgram} (s : Slot p) (bits : Word) (base : Nat) (hb : 3 ≤ base)
    {m : Memory K} {w : Slot p → Word} {P : K → Prop} (h : HeapRep p w m) (hm : Good P m)
    (hbase : m.index recvBaseReg=base) (hcursor : m.index 12=base+bits.length)
    (hz : m.data 0=0) (packet : ScalarPacket m base bits) :
    ∃ t, Eval (Good P) (receiveLoop s) m (14*bits.length+1) t ∧
      HeapRep p (Function.update w s (bits++w s)) t ∧ ReceiveFrame s m t ∧
      t.index freeReg=m.index freeReg+4*bits.length ∧ t.index 12=base := by
  induction bits using List.reverseRecOn generalizing w m with
  | nil =>
    have test : (Cond.addrLT recvBaseReg 12).test m=false := by simp [Cond.test,hbase,hcursor]
    refine ⟨m,Eval.loopFalse test hm,?_,⟨fun _ _ _ => rfl,fun _ _ => rfl⟩,?_,?_⟩
    · simpa only [List.nil_append,Function.update_eq_self] using h
    · simp
    · simpa using hcursor
  | append_singleton bs b ih =>
    have ncur : m.index 12=base+bs.length+1 := by simpa [Nat.add_assoc] using hcursor
    have last : m.data (base+bs.length)=bitScalar b := by
      simpa [List.getElem_append_right (le_refl bs.length)] using packet bs.length (by simp)
    have hbval : m.data (m.index 12-1)=bitScalar b := by rw [ncur,Nat.add_sub_cancel]; exact last
    obtain ⟨u,one,ef,hu⟩ := receiveBody_correct h hm s b hz hbval
    have packetRest : ScalarPacket u base bs := by
      intro i hi
      rw [ef.data _ (by omega)]
      exact (packet i (by simp; omega)).trans
        (congrArg (fun v : Bool => (bitScalar v : K)) (List.getElem_append_left hi))
    have hbase' : u.index recvBaseReg=base :=
      (ef.frame.index _ (ReceiveKeep.header h s (by decide) (by decide))).trans hbase
    have hcursor' : u.index 12=base+bs.length := by rw [ef.cursor,ncur,Nat.add_sub_cancel]
    have hz' : u.data 0=0 := (ef.data 0 (by decide)).trans hz
    obtain ⟨t,rest,heap,frame,f,cur⟩ := ih hu one.safe_end hbase' hcursor' hz' packetRest
    have test : (Cond.addrLT recvBaseReg 12).test m=true := by simp [Cond.test,hbase,ncur]
    have run := Eval.loopTrue test one rest
    refine ⟨t,?_,?_,ef.frame.trans frame (by rw [ef.frontier]; omega),?_,cur⟩
    · simpa [receiveLoop,List.length_append,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using run
    · simpa only [Function.update_self,Function.update_idem,List.append_assoc,List.singleton_append] using heap
    · rw [f,ef.frontier]; simp [Nat.mul_add]; omega

end BitRAM
end LinearProgramming
end Optimization
end OAI

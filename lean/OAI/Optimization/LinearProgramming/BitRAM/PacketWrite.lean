import OAI.Optimization.LinearProgramming.BitRAM.PacketLayout
import OAI.Optimization.LinearProgramming.RAM.Array

/-! A literal RAM traversal converts a reverse binary chain to a forward scalar packet. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace BitRAM

open RAM RAM.Tape OracleSpec

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Address registers 2 and 4 hold the current node and the exclusive end of the packet.
The linked bit selects scalar register 0 or 1, after which the output cursor moves left. -/
def writeReverseBody : Block := Block.straight
  [.incr 6 2, .incr 6 6, .addrLoad 6 6, .load 2 6,
   .decr 4 4, .store 4 2, .addrLoad 2 2]

def writeReverseLoop : Block := .loop (.addrLT nilReg 2) writeReverseBody

/-- `head`, `len` and `base` are register numbers. The block reads their values at entry. -/
def writeReverseChain (head len base : Nat) : Block :=
  .seq (Block.straight [.const 0 0, .const 1 1, .addrCopy 2 head])
    (.seq (seekBlock base 4 8 len) writeReverseLoop)

@[simp] theorem writeReverseChain_size (head len base : Nat) :
    (writeReverseChain head len base).size = 18 := rfl

/-- Complete effects visible outside the reserved scratch area. In particular address registers
24/26, the callback header, all controller heads, and the entire linked heap are preserved. -/
structure PacketWriteEffect (m t : Memory K) (base : Nat) (bits : Word) : Prop where
  packet : ScalarPacket t base bits.reverse
  index : ∀ i, 15 ≤ i → t.index i = m.index i
  data : ∀ i, 3 ≤ i → i < base ∨ base+bits.length ≤ i → t.data i = m.data i

private structure WriteBitEffect (m t : Memory K) (ptr d : Nat) (b : Bool) : Prop where
  link : t.index 2 = m.index ptr
  cursor : t.index 4 = d
  zero : t.data 0 = 0
  one : t.data 1 = 1
  bit : t.data d = bitScalar b
  index : ∀ i, 15 ≤ i → t.index i = m.index i
  data : ∀ i, 3 ≤ i → i ≠ d → t.data i = m.data i

private theorem writeReverseBody_eval {P : K → Prop} {m : Memory K} {ptr d : Nat} {b : Bool}
    (hm : Good P m) (hp : m.index 2 = ptr) (hd : m.index 4 = d+1)
    (low : 31 ≤ ptr) (out : 3 ≤ d) (hb : m.index (ptr+2) = bitNat b)
    (hz : m.data 0 = 0) (ho : m.data 1 = 1) :
    ∃ t, Block.Eval (Good P) writeReverseBody m 7 t ∧ WriteBitEffect m t ptr d b := by
  let u := m.putIndex 6 (ptr+1)
  let v := u.putIndex 6 (ptr+2)
  let a := v.putIndex 6 (bitNat b)
  let c := a.putData 2 (bitScalar b)
  let e := c.putIndex 4 d
  let f := e.putData d (bitScalar b)
  let t := f.putIndex 2 (m.index ptr)
  have bp : P (bitScalar b) := by
    cases b with
    | false => simpa [bitScalar,hz] using hm 0
    | true => simpa [bitScalar,ho] using hm 1
  have hc : Good P c := Memory.AllData.putData (P := P) (m := a) hm 2 bp
  have hf : Good P f := Memory.AllData.putData (P := P) (m := e) hc d bp
  have e1 : Block.Eval (Good P) (.op (.incr 6 2)) m 1 u := by
    simpa [u,hp] using Block.Eval.op_incr m 6 2 hm hm
  have e2 : Block.Eval (Good P) (.op (.incr 6 6)) u 1 v := by
    simpa [u,v] using Block.Eval.op_incr u 6 6 hm hm
  have tag : v.index (v.index 6) = bitNat b := by
    simp [u,v,show ptr+2 ≠ 6 by omega,hb]
  have e3 : Block.Eval (Good P) (.op (.addrLoad 6 6)) v 1 a := by
    simpa [a,tag] using Block.Eval.op_addrLoad v 6 6 hm hm
  have val : a.data (a.index 6) = bitScalar b := by cases b <;> simp [a,v,u,bitNat,bitScalar,hz,ho]
  have e4 : Block.Eval (Good P) (.op (.load 2 6)) a 1 c := by
    simpa [c,val] using Block.Eval.op_load (safe := Good P) a 2 6 hm (Memory.AllData.putData (m := a) hm 2 (hm _))
  have dc : c.index 4 - 1 = d := by simp [c,a,v,u,hd]
  have e5 : Block.Eval (Good P) (.op (.decr 4 4)) c 1 e := by
    simpa [e,dc] using Block.Eval.op_decr c 4 4 hc hc
  have ev : e.data 2 = bitScalar b := by simp [e,c]
  have ei : e.index 4 = d := by simp [e]
  have e6 : Block.Eval (Good P) (.op (.store 4 2)) e 1 f := by
    simpa [f,ei,ev] using Block.Eval.op_store (safe := Good P) e 4 2 hc (Memory.AllData.putData (m := e) hc _ (hc 2))
  have link : f.index (f.index 2) = m.index ptr := by
    simp [f,e,c,a,v,u,hp,show ptr ≠ 4 by omega,show ptr ≠ 6 by omega]
  have e7 : Block.Eval (Good P) (.op (.addrLoad 2 2)) f 1 t := by
    simpa [t,link] using Block.Eval.op_addrLoad f 2 2 hf hf
  refine ⟨t,e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq (.skip hf))))))),?_⟩
  refine ⟨by simp [t], by simp [t,f,e], ?_, ?_, by simp [t,f], ?_, ?_⟩
  · simp [t,f,e,c,a,v,u,show 0 ≠ d by omega,hz]
  · simp [t,f,e,c,a,v,u,show 1 ≠ d by omega,ho]
  · intro i hi
    simp [t,f,e,c,a,v,u,show i ≠ 2 by omega,show i ≠ 4 by omega,show i ≠ 6 by omega]
  · intro i hi hne
    simp [t,f,e,c,a,v,u,hne,show i ≠ 2 by omega]

private theorem writeReverseLoop_eval {P : K → Prop} {lo hi base : Nat} (bits : Word)
    (hl : 31 ≤ lo) (hb : 3 ≤ base) {m : Memory K} {ptr : Nat}
    (hm : Good P m) (hptr : m.index 2 = ptr) (hcursor : m.index 4 = base+bits.length)
    (hc : Chain m.index lo hi ptr bits) (hnil : m.index nilReg = 0)
    (hz : m.data 0 = 0) (ho : m.data 1 = 1) :
    ∃ t, Block.Eval (Good P) writeReverseLoop m (9*bits.length+1) t ∧
      PacketWriteEffect m t base bits := by
  induction bits generalizing m ptr with
  | nil =>
    cases hc
    have test : (Cond.addrLT nilReg 2).test m = false := by simp [Cond.test,hnil,hptr]
    exact ⟨m, .loopFalse test hm, ScalarPacket.nil _ _, fun _ _ => rfl, fun _ _ _ => rfl⟩
  | cons b bs ih =>
    cases hc with
    | @cons ptr _ _ low _ _ tag tail =>
      have runCursor : m.index 4 = (base+bs.length)+1 := by simpa [Nat.add_assoc] using hcursor
      obtain ⟨u, one, ef⟩ := writeReverseBody_eval hm hptr runCursor (hl.trans low)
        (show 3 ≤ base+bs.length by omega) tag hz ho
      have tail' : Chain u.index lo hi (m.index ptr) bs :=
        tail.transport le_rfl (fun i hi _ _ => ef.index i (by omega))
      have unil : u.index nilReg = 0 := (ef.index _ (by decide)).trans hnil
      obtain ⟨t, rest, done⟩ := ih one.safe_end ef.link ef.cursor tail' unil ef.zero ef.one
      have test : (Cond.addrLT nilReg 2).test m = true := by
        simp only [Cond.test,hnil,hptr,decide_eq_true_eq]; omega
      refine ⟨t, ?_, ?_⟩
      · have run := Block.Eval.loopTrue test one rest
        simpa [writeReverseLoop,List.length_cons,Nat.mul_add,Nat.add_assoc,Nat.add_comm,
          Nat.add_left_comm] using run
      · refine ⟨?_,fun i hi => (done.index i hi).trans (ef.index i hi),?_⟩
        · rw [List.reverse_cons]
          apply done.packet.snoc
          have ext := done.data (base+bs.length) (by omega) (Or.inr le_rfl)
          simpa using ext.trans ef.bit
        · intro i hi outside
          have endv : i < base ∨ base+bs.length ≤ i := by simp only [List.length_cons] at outside; omega
          have ne : i ≠ base+bs.length := by simp only [List.length_cons] at outside; omega
          exact (done.data i hi endv).trans (ef.data i hi ne)

/-- Literal primitive instruction count for the complete conversion. The base and length
registers may coincide and may refer to controller headers. The routine uses address registers
2, 4, 6 and 8 as scratch. -/
theorem writeReverseChain_correct {P : K → Prop} {m : Memory K} {lo hi : Nat}
    (head len base : Nat) (bits : Word) (hm : Good P m) (zero : P 0) (one : P 1)
    (hlo : 31 ≤ lo) (hlen : 15 ≤ len) (hbase : 15 ≤ base)
    (out : 3 ≤ m.index base) (width : m.index len = bits.length)
    (hc : Chain m.index lo hi (m.index head) bits) (hnil : m.index nilReg = 0) :
    ∃ t, Block.Eval (Good P) (writeReverseChain head len base) m (13*bits.length+7) t ∧
      PacketWriteEffect m t (m.index base) bits := by
  let x := m.putData 0 0
  let y := x.putData 1 1
  let z := y.putIndex 2 (m.index head)
  have hx : Good P x := Memory.AllData.putData hm 0 zero
  have hy : Good P y := Memory.AllData.putData hx 1 one
  have e0 : Block.Eval (Good P) (.op (.const 0 0)) m 1 x := by
    simpa [x] using Block.Eval.op_const m 0 0 hm (by simpa using hx)
  have e1 : Block.Eval (Good P) (.op (.const 1 1)) x 1 y := by
    simpa [y] using Block.Eval.op_const x 1 1 hx (by simpa using hy)
  have e2 : Block.Eval (Good P) (.op (.addrCopy 2 head)) y 1 z :=
    Block.Eval.op_addrCopy y 2 head hy hy
  have ez : Block.Eval (Good P) (.straight [.const 0 0,.const 1 1,.addrCopy 2 head]) m 3 z :=
    e0.seq (e1.seq (e2.seq (.skip hy)))
  have lenZ : z.index len = bits.length := by simp [z,y,x,show len ≠ 2 by omega,width]
  obtain ⟨u, seek, sdata, _, cursor, sf⟩ := seekBlock_correct P z base 4 8 len bits.length
    (by decide) (by omega) (by omega) lenZ hy
  have idx : ∀ i, 15 ≤ i → u.index i = m.index i := by
    intro i hi
    rw [sf i (by omega) (by omega)]
    simp [z,y,x,show i ≠ 2 by omega]
  have ptr : u.index 2 = m.index head := by rw [sf 2 (by decide) (by decide)]; simp [z]
  have hp : u.index 4 = m.index base + bits.length := by
    simpa [z,y,x,show base ≠ 2 by omega] using cursor
  have chain : Chain u.index lo hi (m.index head) bits := hc.transport le_rfl (fun i h _ _ => idx i (by omega))
  have nilU : u.index nilReg = 0 := (idx _ (by decide)).trans hnil
  have zeroU : u.data 0 = 0 := by rw [sdata]; simp [z,y,x]
  have oneU : u.data 1 = 1 := by rw [sdata]; simp [z,y]
  obtain ⟨t, run, eff⟩ := writeReverseLoop_eval bits hlo out seek.safe_end ptr hp chain nilU zeroU oneU
  refine ⟨t, ?_,eff.packet,fun i h => (eff.index i h).trans (idx i h),?_⟩
  · have both := ez.seq (seek.seq run)
    rw [show 13*bits.length+7 = 3+(4*bits.length+3+(9*bits.length+1)) by omega]
    exact both
  · intro i hi hout
    rw [eff.data i hi hout,sdata]
    simp [z,y,x,show i ≠ 0 by omega,show i ≠ 1 by omega]

/-- The physical callback copies the pending reverse emitter buffer into its public send packet. -/
def preparePacket : Block := writeReverseChain bufferReg bufferLenReg sendBaseReg

theorem preparePacket_heap_correct {P : K → Prop} {p : BitProgram} {w : Slot p → Word} {m : Memory K}
    (h : HeapRep p w m) (hm : Good P m) (zero : P 0) (one : P 1) (base : 3 ≤ m.index sendBaseReg)
    (width : m.index bufferLenReg = (w none).length) :
    ∃ t, Block.Eval (Good P) preparePacket m (13*(w none).length+7) t ∧ HeapRep p w t ∧
      PacketWriteEffect m t (m.index sendBaseReg) (w none) := by
  obtain ⟨t, run, ef⟩ := writeReverseChain_correct bufferReg bufferLenReg sendBaseReg (w none)
    hm zero one (show 31 ≤ heapStart p by unfold heapStart; omega) (by decide) (by decide) base
    width (h.chain none) h.nilValue
  exact ⟨t,run,h.of_odd_eq (fun i hi _ => ef.index i (by omega)),ef⟩

theorem preparePacket_correct {P : K → Prop} {p : BitProgram} {c : p.Config} {m : Memory K}
    (h : Rep p c m) (hm : Good P m) (zero : P 0) (one : P 1) (base : 3 ≤ m.index sendBaseReg) :
    ∃ t, Block.Eval (Good P) preparePacket m (13*c.bufferRev.length+7) t ∧ Rep p c t ∧
      PacketWriteEffect m t (m.index sendBaseReg) c.bufferRev := by
  obtain ⟨t, run, ef⟩ := writeReverseChain_correct bufferReg bufferLenReg sendBaseReg c.bufferRev
    hm zero one (show 31 ≤ heapStart p by unfold heapStart; omega) (by decide) (by decide) base
    h.bufferLength (h.heap.chain none) h.heap.nilValue
  exact ⟨t,run,h.of_odd_eq (fun i hi _ => ef.index i (by omega)),ef⟩

/-- Standalone execution as an ordinary instruction-by-instruction RAM trace, including halt. -/
theorem preparePacket_trace {P : K → Prop} {p : BitProgram} {c : p.Config} {m : Memory K}
    (h : Rep p c m) (hm : Good P m) (zero : P 0) (one : P 1) (base : 3 ≤ m.index sendBaseReg)
    (tag : Nat) :
    let time := (13*c.bufferRev.length+7)+1
    ∃ states : Fin (time+1) → State K, Trace (preparePacket.compile 0 ++ [.halt tag]) (m.atPC 0) time states ∧
      (states (Fin.last time)).output = some tag ∧ Rep p c (states (Fin.last time)).memory ∧
      PacketWriteEffect m (states (Fin.last time)).memory (m.index sendBaseReg) c.bufferRev ∧
      ∀ i, Good P (states i).memory := by
  obtain ⟨t,run,rep,ef⟩ := preparePacket_correct h hm zero one base
  obtain ⟨states,trace,out,last,safe⟩ := run.halted_trace (tag := tag)
  exact ⟨states,trace,out,last.symm ▸ rep,last.symm ▸ ef,safe⟩

end BitRAM
end LinearProgramming
end Optimization
end OAI

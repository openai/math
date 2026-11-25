import OAI.Optimization.LinearProgramming.Compression.TaggedClock
import OAI.Optimization.LinearProgramming.RAM.CallableBase
import OAI.Optimization.LinearProgramming.Compression.BinaryWireComponents
import OAI.Optimization.LinearProgramming.Compression.BinaryWireTags
import OAI.Optimization.LinearProgramming.Compression.BinaryPacketParts

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM BitRAM OracleSpec OracleSpec.MinorLog NativePrice

private def decodeSomeFlatReply : Block :=
  .seq packetRationalParts (.seq publishWireComponents (replyMark true))

/-- Decode the native output packet `[false]` or `true :: encodeRat q` at address 43.
The result marker permits distinct return continuations in the caller. -/
def decodeTaggedFlatReply : Block := .seq promoteFlatReply <| .seq captureFlatTag <|
  .branch (.scalarLT 7 5) (replyMark false) decodeSomeFlatReply

theorem decodeTaggedFlatReply_spec (m : Memory ℚ) (r : Option ℚ) (limit : ℕ)
    (hm : m.AllData (fun z => ratBits z ≤ limit)) (base : 3 ≤ m.index 43)
    (len : m.index 37=(optionalRationalWord r).length)
    (packet : ScalarPacket m (m.index 43) (optionalRationalWord r))
    (budget : 2*(optionalRationalWord r).length+7 ≤ limit) :
    ∃ s t, Block.Eval (Memory.AllData (fun z=>ratBits z ≤ limit)) decodeTaggedFlatReply m s t ∧
      s+2 ≤ taggedReplyClock (optionalRationalWord r).length ∧ TaggedReady t r := by
  let P := fun z : ℚ => ratBits z ≤ limit
  have h0 : P 0 := by change 3 ≤ limit; omega
  have h1 : P 1 := by change 3 ≤ limit; omega
  obtain ⟨a,promote,la,pa,wa⟩ := promoteFlatReply_spec m (optionalRationalWord r) hm len base packet
  cases r with
  | none =>
    obtain ⟨b,tag,flag,one,_,_,_⟩ := captureFlatTag_spec a false [] promote.safe_end h1 pa wa
    obtain ⟨t,mark,cmp,_,_⟩ := replyMark_spec b false tag.safe_end h0 h1
    have yes : (Cond.scalarLT 7 5).test b=true := by simp [Cond.test,flag,one]
    refine ⟨_,t,promote.seq (tag.seq (.branchTrue yes mark)),?_,?_⟩
    · unfold taggedReplyClock; omega
    · intro h; exact Bool.false_ne_true (cmp.mp h)
  | some q =>
    let k := (optionalRationalWord (some q)).length
    have short : (encodeRat q).length ≤ k := Nat.le_succ _
    obtain ⟨b,tag,flag,one,bl,bc,payload⟩ := captureFlatTag_spec a true (encodeRat q) promote.safe_end h1 pa wa
    have no : (Cond.scalarLT 7 5).test b=false := by simp [Cond.test,flag,one]
    obtain ⟨c,s,cs,parts,num,den,_,_,fi⟩ := packetRationalParts_bits q b (b.index 3) limit rfl
      (by omega) payload tag.safe_end
    have hmax : max limit (3+(encodeRat q).length)=limit := Nat.max_eq_left (by omega)
    rw [hmax] at parts
    have c37 : c.index 37=k := (fi 37 (Or.inr (by decide))).trans (bl.trans la)
    obtain ⟨l,d,emit,ce,out⟩ := publishWireComponents_spec c q k limit parts.safe_end c37 budget short num den
    obtain ⟨t,mark,cmp,fd,idx⟩ := replyMark_spec d true emit.safe_end h0 h1
    refine ⟨_,t,promote.seq (tag.seq (.branchFalse no (parts.seq (emit.seq mark)))),?_,cmp.mpr rfl,?_⟩
    · change _ ≤ taggedReplyClock k
      unfold taggedReplyClock
      change _ ≤ 16*(encodeRat q).length+27 at cs
      dsimp only [k] at short ce ⊢
      omega
    · exact explicitValue_preserve_output out fd idx

/-- Append the two genuine halts to an arbitrary correctly marked caller fragment. -/
def finishTaggedFragment (f : RAM.Callable.Fragment) : Program := f.emit 0 ++
  [.branchLT 5 6 (f.size+1) (f.size+2),.halt 0,.halt 1]

theorem finishTaggedFragment_run (f : RAM.Callable.Fragment) (m z : Memory ℚ) (r : Option ℚ)
    (limit clock : ℕ) (exec : f.Run (fun x=>ratBits x ≤ limit) m clock z) (result : TaggedReady z r) :
    ∃ t, call (finishTaggedFragment f) (clock+2) limit (m.atPC 0) t ∧ emits t r := by
  let e := f.size
  let p := finishTaggedFragment f
  let ops : List Instr := [.branchLT 5 6 (e+1) (e+2),.halt 0,.halt 1]
  have all : CodeAt p 0 (f.emit 0 ++ ops) := CodeAt.whole _
  have tail : CodeAt p e ops := by simpa only [f.length_emit,Nat.zero_add,e] using all.right
  have dispatch : p[e]?=some (.branchLT 5 6 (e+1) (e+2)) := tail.head
  have next : CodeAt p (e+1) [.halt 0,.halt 1] := Block.Eval.tail_at tail
  have yes : p[e+1]?=some (.halt 0) := next.head
  have no : p[e+2]?=some (.halt 1) := (Block.Eval.tail_at next).head
  obtain ⟨s,cost,go⟩ := exec p 0 all.left
  rw [Nat.zero_add] at go
  cases r with
  | none =>
    have hcmp : ¬z.data 5 < z.data 6 := result
    have jump : Execution p (scalarBound limit) (z.atPC e) 1 (z.atPC (e+2)) := by
      apply Execution.one go.safe_end _ go.safe_end
      simp [step,Memory.atPC,dispatch,execInstr,hcmp]
    let t : State ℚ := {z.atPC (e+2) with output:=some 1}
    have stop : Execution p (scalarBound limit) (z.atPC (e+2)) 1 t := by
      apply Execution.one go.safe_end _ go.safe_end
      simp [step,Memory.atPC,no,execInstr,t]
    obtain ⟨tr,ht,last,safe⟩ := ((go.append jump).append stop).to_trace
    exact ⟨t,⟨_,by omega,tr,ht,last,safe⟩,rfl⟩
  | some q =>
    obtain ⟨cmp,out⟩ := result
    have jump : Execution p (scalarBound limit) (z.atPC e) 1 (z.atPC (e+1)) := by
      apply Execution.one go.safe_end _ go.safe_end
      simp [step,Memory.atPC,dispatch,execInstr,cmp]
    let t : State ℚ := {z.atPC (e+1) with output:=some 0}
    have stop : Execution p (scalarBound limit) (z.atPC (e+1)) 1 t := by
      apply Execution.one go.safe_end _ go.safe_end
      simp [step,Memory.atPC,yes,execInstr,t]
    obtain ⟨tr,ht,last,safe⟩ := ((go.append jump).append stop).to_trace
    exact ⟨t,⟨_,by omega,tr,ht,last,safe⟩,rfl,explicitValue_of_memory (m:=z) rfl out⟩

/-- The stand-alone adapter reads the packet length and base at addresses 37 and 43. -/
def taggedFlatReplyProgram : Program := finishTaggedFragment (.ofBlock decodeTaggedFlatReply)

theorem taggedFlatReply_call (m : Memory ℚ) (r : Option ℚ) (limit : ℕ)
    (hm : m.AllData (fun z => ratBits z ≤ limit)) (base : 3 ≤ m.index 43)
    (len : m.index 37=(optionalRationalWord r).length)
    (packet : ScalarPacket m (m.index 43) (optionalRationalWord r))
    (budget : 2*(optionalRationalWord r).length+7 ≤ limit) :
    ∃ t, call taggedFlatReplyProgram (taggedReplyClock (optionalRationalWord r).length) limit (m.atPC 0) t ∧ emits t r := by
  obtain ⟨s,z,block,cost,out⟩ := decodeTaggedFlatReply_spec m r limit hm base len packet budget
  obtain ⟨t,⟨l,clock,tr,go,last,safe⟩,em⟩ := finishTaggedFragment_run (.ofBlock decodeTaggedFlatReply) m z r limit s
    (RAM.Callable.Fragment.Run.ofBlock block) out
  exact ⟨t,⟨l,clock.trans cost,tr,go,last,safe⟩,em⟩

end Compression
end LinearProgramming
end Optimization
end OAI

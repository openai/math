import OAI.Optimization.LinearProgramming.Compression.MetadataPacket

/-! Prepare the public scalar-wire cursor and append a Boolean stored in an address register. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace Inner
namespace Metadata

variable {K : Type*}

open RAM BitRAM OracleSpec

def initializeBlock : Block := .seq (.op (.const 0 0)) <| .seq (.op (.const 2 1)) <|
  .seq (.op (.addrCopy 65 47)) <| .seq (.op (.addrConst 49 0)) <|
  .seq (.op (.addrConst 67 0)) (.op (.addrConst 75 1))

structure Started [Zero K] [One K] (s t : Memory K) : Prop where
  ready : Ready t
  cursor : t.index 65=s.index 47
  length : t.index 49=0
  data : ∀ i, 3 ≤ i → t.data i=s.data i
  frame : ∀ i, i≠49 → i≠65 → i≠67 → i≠75 → t.index i=s.index i

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {P : K → Prop}

theorem initialize_correct (s : Memory K) (hs : s.AllData P) (hz : P 0) (ho : P 1) (base : 3 ≤ s.index 47) :
    ∃ t, Block.Eval (Memory.AllData P) initializeBlock s 6 t ∧ Started s t := by
  let a := s.putData 0 0
  let b := a.putData 2 1
  let c := b.putIndex 65 (b.index 47)
  let d := c.putIndex 49 0
  let e := d.putIndex 67 0
  let f := e.putIndex 75 1
  have az := hs.putData 0 hz
  have ha : Block.Eval (Memory.AllData P) (.op (.const 0 0)) s 1 a := by
    simpa only [Rat.cast_zero] using Block.Eval.op_const s 0 0 hs (by simpa only [Rat.cast_zero] using az)
  have bo := ha.safe_end.putData 2 ho
  have hb : Block.Eval (Memory.AllData P) (.op (.const 2 1)) a 1 b := by
    simpa only [Rat.cast_one] using Block.Eval.op_const a 2 1 ha.safe_end (by simpa only [Rat.cast_one] using bo)
  have hc : Block.Eval (Memory.AllData P) (.op (.addrCopy 65 47)) b 1 c :=
    Block.Eval.op_addrCopy _ _ _ hb.safe_end hb.safe_end
  have hd : Block.Eval (Memory.AllData P) (.op (.addrConst 49 0)) c 1 d :=
    Block.Eval.op_addrConst _ _ _ hc.safe_end hc.safe_end
  have he : Block.Eval (Memory.AllData P) (.op (.addrConst 67 0)) d 1 e :=
    Block.Eval.op_addrConst _ _ _ hd.safe_end hd.safe_end
  have hf : Block.Eval (Memory.AllData P) (.op (.addrConst 75 1)) e 1 f :=
    Block.Eval.op_addrConst _ _ _ he.safe_end he.safe_end
  refine ⟨f,ha.seq (hb.seq (hc.seq (hd.seq (he.seq hf)))),?_,?_,?_,?_,?_⟩
  · constructor <;> simp [f,e,d,c,b,a,base]
  · simp [f,e,d,c,b,a]
  · simp [f,e,d,c]
  · intro i hi
    simp [f,e,d,c,b,a,show i≠0 by omega,show i≠2 by omega]
  · intro i h49 h65 h67 h75
    simp [f,e,d,c,b,a,h49,h65,h67,h75]

def emitFromBit (header : Nat) : Block := .branch (.addrLT 67 header) (emit true) (emit false)

theorem emitFromBit_correct (s : Memory K) (header : Nat) (b : Bool) (hs : s.AllData P) (ready : Ready s)
    (hv : s.index header=b.toNat) :
    ∃ t k, Block.Eval (Memory.AllData P) (emitFromBit header) s k t ∧ k ≤ 5 ∧ Effect s t [b] := by
  cases b with
  | false =>
    obtain ⟨t,run,ef,_⟩ := emit_correct s false hs ready
    have test : (Cond.addrLT 67 header).test s = false := by simp [Cond.test,ready.indexZero,hv]
    exact ⟨t,4,Block.Eval.branchFalse test run,by decide,ef⟩
  | true =>
    obtain ⟨t,run,ef,_⟩ := emit_correct s true hs ready
    have test : (Cond.addrLT 67 header).test s = true := by simp [Cond.test,ready.indexZero,hv]
    exact ⟨t,5,Block.Eval.branchTrue test run,by decide,ef⟩

end Metadata
end Inner
end Compression
end LinearProgramming
end Optimization
end OAI

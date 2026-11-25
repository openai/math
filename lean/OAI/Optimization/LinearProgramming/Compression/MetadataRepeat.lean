import OAI.Optimization.LinearProgramming.Compression.MetadataPacket

/-! Emit the repeated pair used by the unary metadata codec and the little-endian
power-of-two field of the LP's price-game epoch. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace Inner
namespace Metadata

variable {K : Type*}
open RAM OracleSpec BitRAM

private theorem setCount_effect [Zero K] [One K] (s : Memory K) (a : Nat) :
    Effect s (s.putIndex 69 a) [] :=
  Effect.empty rfl (Memory.putIndex_ne _ (by decide : 65 ≠ 69) _)
    (Memory.putIndex_ne _ (by decide : 49 ≠ 69) _)
    (fun i _ _ h69 _ => Memory.putIndex_ne s h69 a)

def repeatPairBody (bit : Bool) : Block := .seq (emit true) (.seq (emit bit) (.op (.decr 69 69)))

def repeatPairLoop (bit : Bool) : Block := .loop (.addrLT 67 69) (repeatPairBody bit)

/-- Read the repetition count once, then emit the finite bit pair through the public
scalar cursor. The caller emits any tag or delimiter following this block. -/
def repeatPairFrom (header : Nat) (bit : Bool) : Block :=
  .seq (.op (.addrCopy 69 header)) (repeatPairLoop bit)

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {P : K → Prop}

private theorem repeatPairLoop_correct (n : Nat) (bit : Bool) (s : Memory K)
    (hs : s.AllData P) (ready : Ready s) (counter : s.index 69=n) :
    ∃ t, Block.Eval (Memory.AllData P) (repeatPairLoop bit) s (9*n+1) t ∧
      Effect s t ((List.replicate n ([true,bit] : Word)).flatten) := by
  induction n generalizing s with
  | zero =>
    have stop : (Cond.addrLT 67 69).test s=false := by simp [Cond.test,ready.indexZero,counter]
    exact ⟨s,Block.Eval.loopFalse stop hs,Effect.refl _⟩
  | succ n ih =>
    obtain ⟨a,first,fa,ra⟩ := emit_correct s true hs ready
    obtain ⟨b,second,fb,rb⟩ := emit_correct a bit first.safe_end (ready.after fa)
    let c := b.putIndex 69 (b.index 69-1)
    have last : Block.Eval (Memory.AllData P) (.op (.decr 69 69)) b 1 c :=
      Block.Eval.op_decr _ _ _ second.safe_end second.safe_end
    have before : b.index 69=n+1 := (rb 69 (by decide) (by decide)).trans ((ra 69 (by decide) (by decide)).trans counter)
    have smaller : c.index 69=n := by simp [c,before]
    have chunk : Effect s c [true,bit] := by simpa [c] using (fa.append fb).append (setCount_effect b (b.index 69-1))
    obtain ⟨t,tail,ft⟩ := ih c last.safe_end (ready.after chunk) smaller
    have test : (Cond.addrLT 67 69).test s=true := by simp [Cond.test,ready.indexZero,counter]
    have body : Block.Eval (Memory.AllData P) (repeatPairBody bit) s 7 c := first.seq (second.seq last)
    refine ⟨t,?_,?_⟩
    · rw [show 9*(n+1)+1=1+7+1+(9*n+1) by omega]
      exact Block.Eval.loopTrue test body tail
    · simpa only [List.replicate_succ,List.flatten_cons] using chunk.append ft

theorem repeatPairFrom_correct (header : Nat) (bit : Bool) (n : Nat) (s : Memory K)
    (hs : s.AllData P) (ready : Ready s) (count : s.index header=n) :
    ∃ t k, Block.Eval (Memory.AllData P) (repeatPairFrom header bit) s k t ∧ k≤10*n+3 ∧
      Effect s t ((List.replicate n ([true,bit] : Word)).flatten) := by
  let a := s.putIndex 69 (s.index header)
  have setup : Block.Eval (Memory.AllData P) (.op (.addrCopy 69 header)) s 1 a :=
    Block.Eval.op_addrCopy _ _ _ hs hs
  have empty := setCount_effect s (s.index header)
  obtain ⟨t,loop,done⟩ := repeatPairLoop_correct n bit a setup.safe_end (ready.after empty) (by simp [a,count])
  exact ⟨t,_,setup.seq loop,by omega,by simpa only [List.nil_append] using empty.append done⟩

end Metadata
end Inner
end Compression
end LinearProgramming
end Optimization
end OAI

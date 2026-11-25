import OAI.Optimization.LinearProgramming.RAM.Array

/-! Division by two on a small address value without reading the bits of any scalar. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace Inner
namespace Metadata

open RAM

def halveBody : Block := .seq (.op (.decr 69 69))
  (.seq (.op (.decr 69 69)) (.op (.incr 71 71)))

def halveLoop : Block := .loop (.addrLT 75 69) halveBody

def halve : Block := .seq (.op (.addrConst 71 0)) halveLoop

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {P : K → Prop}

private theorem halveLoop_correct (q r : Nat) (hr : r ≤ 1) (s : Memory K) (hs : s.AllData P)
    (value : s.index 69 = 2*q+r) (one : s.index 75 = 1) :
    ∃ t, Block.Eval (Memory.AllData P) halveLoop s (5*q+1) t ∧ t.data=s.data ∧
      t.index 69=r ∧ t.index 71=s.index 71+q ∧ ∀ i, i≠69 → i≠71 → t.index i=s.index i := by
  induction q generalizing s with
  | zero =>
    have h : (Cond.addrLT 75 69).test s=false := by simp [Cond.test,one,value,Nat.not_lt_of_ge hr]
    exact ⟨s,Block.Eval.loopFalse h hs,rfl,by simpa using value,by simp,fun _ _ _ => rfl⟩
  | succ q ih =>
    let a := s.putIndex 69 (s.index 69-1)
    let b := a.putIndex 69 (a.index 69-1)
    let c := b.putIndex 71 (b.index 71+1)
    have ha : Block.Eval (Memory.AllData P) (.op (.decr 69 69)) s 1 a :=
      Block.Eval.op_decr _ _ _ hs hs
    have hb : Block.Eval (Memory.AllData P) (.op (.decr 69 69)) a 1 b :=
      Block.Eval.op_decr _ _ _ ha.safe_end ha.safe_end
    have hc : Block.Eval (Memory.AllData P) (.op (.incr 71 71)) b 1 c :=
      Block.Eval.op_incr _ _ _ hb.safe_end hb.safe_end
    have body : Block.Eval (Memory.AllData P) halveBody s 3 c := ha.seq (hb.seq hc)
    have v : c.index 69=2*q+r := by simp [c,b,a,value]; omega
    have l : c.index 71=s.index 71+1 := by simp [c,b,a]
    obtain ⟨t,rest,data,remd,out,idx⟩ := ih c hc.safe_end v (by simp [c,b,a,one])
    have ht : (Cond.addrLT 75 69).test s=true := by simp [Cond.test,one,value]; omega
    refine ⟨t,?_,data,remd,by rw [out,l]; omega,?_⟩
    · change Block.Eval (Memory.AllData P) (.loop (.addrLT 75 69) halveBody) s (5*(q+1)+1) t
      rw [show 5*(q+1)+1 = 1+3+1+(5*q+1) by omega]
      exact Block.Eval.loopTrue ht body rest
    · intro i h69 h71
      simpa [c,b,a,h69,h71] using idx i h69 h71

/-- Register 69 holds the low bit, register 71 the quotient. All scalar cells and
all other address cells are unchanged. Only comparison, decrement and increment are used. -/
theorem halve_correct (s : Memory K) (value : Nat) (hs : s.AllData P)
    (hv : s.index 69=value) (one : s.index 75=1) :
    ∃ t, Block.Eval (Memory.AllData P) halve s (5*(value/2)+2) t ∧ t.data=s.data ∧
      t.index 69=value%2 ∧ t.index 71=value/2 ∧ ∀ i, i≠69 → i≠71 → t.index i=s.index i := by
  let a := s.putIndex 71 0
  have ha : Block.Eval (Memory.AllData P) (.op (.addrConst 71 0)) s 1 a :=
    Block.Eval.op_addrConst _ _ _ hs hs
  obtain ⟨t,hloop,hd,hrem,hq,frame⟩ := halveLoop_correct (value/2) (value%2) (by omega) a
    ha.safe_end (by simp [a,hv]; omega) (by simp [a,one])
  exact ⟨t,by simpa only [halve,show 1+(5*(value/2)+1)=5*(value/2)+2 by omega] using ha.seq hloop,
    hd,hrem,by simpa [a] using hq,fun i h69 h71 => by simpa [a,h71] using frame i h69 h71⟩

end Metadata
end Inner
end Compression
end LinearProgramming
end Optimization
end OAI

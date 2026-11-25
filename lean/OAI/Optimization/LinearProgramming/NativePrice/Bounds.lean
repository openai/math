import OAI.Optimization.LinearProgramming.RAM.Array

/-! Materialize the declared end of the price packet and test it against the consumed cursor. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace NativePrice

open RAM

def boundsBlock : Block :=
  .seq (.op (.addrCopy 3 43)) <| .seq (.op (.addrCopy 12 43))
    (.forRange 13 37 (.op (.incr 12 12)))

/-- Set scalar-tape cursor 3 and exclusive end 12 using the actual declared length. -/
theorem boundsBlock_spec {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (s : Memory K) (hs : s.AllData P) :
    ∃ t, Block.Eval (Memory.AllData P) boundsBlock s (4*s.index 37+4) t ∧
      t.data=s.data ∧ t.index 3=s.index 43 ∧ t.index 12=s.index 43+s.index 37 ∧
      ∀ j, j≠3 → j≠12 → j≠13 → t.index j=s.index j := by
  let a := s.putIndex 3 (s.index 43)
  let m := a.putIndex 12 (a.index 43)
  have ea := Block.Eval.op_addrCopy s 3 43 hs hs
  have em := Block.Eval.op_addrCopy a 12 43 ea.safe_end ea.safe_end
  let I := fun (j : ℕ) (u : Memory K) => u.AllData P ∧ u.index 13=j ∧
    u.index 37=s.index 37 ∧ u.index 3=s.index 43 ∧ u.index 12=s.index 43+j ∧
    u.data=s.data ∧ ∀ q, q≠3 → q≠12 → q≠13 → u.index q=s.index q
  have init : I 0 (m.putIndex 13 0) := by
    refine ⟨em.safe_end,?_,?_,?_,?_,rfl,?_⟩
    · simp
    · simp [m,a]
    · simp [m,a]
    · simp [m,a]
    · intro q h3 h12 h13
      simp [m,a,h3,h12,h13]
  have body (j : ℕ) (_ : j<s.index 37) (u : Memory K) (h : I j u) :
      ∃ v, Block.Eval (Memory.AllData P) (.op (.incr 12 12)) u 1 v ∧
        I (j+1) (v.putIndex 13 (v.index 13+1)) := by
    obtain ⟨safe,cnt,len,cur,pos,data,idx⟩ := h
    let v := u.putIndex 12 (u.index 12+1)
    refine ⟨v,Block.Eval.op_incr u 12 12 safe safe,safe,?_,?_,?_,?_,data,?_⟩
    · simp [v,cnt]
    · simpa [v] using len
    · simpa [v] using cur
    · simp [v,pos,Nat.add_assoc]
    · intro q h3 h12 h13
      simpa [v,h12,h13] using idx q h3 h12 h13
  obtain ⟨t,e,_,_,_,cur,pos,data,idx⟩ := Block.Eval.forRange_invariant_exact 13 37
    (s.index 37) 1 I m em.safe_end init (fun _ _ h => ⟨h.1,h.2.1,h.2.2.1⟩) body
  refine ⟨t,?_,data,cur,pos,idx⟩
  simpa only [boundsBlock,show 1+(1+(s.index 37*(1+3)+2))=4*s.index 37+4 by omega] using ea.seq (em.seq e)

def checkEnd : Block := .branch (.addrLT 3 12) (.op (.addrConst 13 0))
  (.branch (.addrLT 12 3) (.op (.addrConst 13 0)) (.op (.addrConst 13 1)))

/-- The success value is written only after comparing the cursor with the declared end. -/
theorem checkEnd_spec {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (s : Memory K) (hs : s.AllData P) (h : s.index 3=s.index 12) :
    Block.Eval (Memory.AllData P) checkEnd s 3 (s.putIndex 13 1) := by
  exact .branchFalse (by simp [Cond.test,h]) (.branchFalse (by simp [Cond.test,h])
    (Block.Eval.op_addrConst s 13 1 hs hs))

end NativePrice
end LinearProgramming
end Optimization
end OAI

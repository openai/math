import OAI.Optimization.LinearProgramming.Compression.MinorProxyInputsStep

/-! Construct the shared denominator 2^(precision+2) using exactly one scalar doubling per bit. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace MinorProxyCache
open RAM

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def writeScale : Block := .seq (.op (.const 0 4))
  (.seq (.forRange 63 85 (.op (.add 0 0 0))) (.op (.store 86 0)))

theorem writeScale_eval (P : K→Prop) (m : Memory K) (hs : m.AllData P) (prec : ℕ)
    (hp : m.index 85=prec) (powers : ∀ k≤prec, P ((2:K)^(k+2))) :
    ∃ t, Block.Eval (Memory.AllData P) writeScale m (prec*4+4) t ∧
      t.data (m.index 86)=(2:K)^(prec+2) ∧
      (∀j, j≠0 → j≠m.index 86 → t.data j=m.data j) ∧
      ∀j, j≠63 → t.index j=m.index j := by
  let a := m.putData 0 4
  have h4 : P (4:K) := by
    have eq : (2:K)^(0+2)=4 := by norm_num
    exact eq ▸ powers 0 (by omega)
  have ha : a.AllData P := hs.putData 0 h4
  have init : Block.Eval (Memory.AllData P) (.op (.const 0 4)) m 1 a := by
    simpa [a] using Block.Eval.op_const m 0 4 hs (by simpa [a] using ha)
  let I (k : ℕ) (s : Memory K) := s.AllData P ∧ s.index 63=k ∧ s.data 0=(2:K)^(k+2) ∧
    (∀j,j≠0 → s.data j=m.data j) ∧ (∀j,j≠63 → s.index j=m.index j)
  have start : I 0 (a.putIndex 63 0) := by
    refine ⟨ha,by simp,by norm_num [a],?_,?_⟩
    · intro j h; simp [a,h]
    · intro j h; simp [a,h]
  obtain ⟨u,dbl,done⟩ := Block.Eval.forRange_invariant_exact (safe := Memory.AllData P) 63 85 prec 1 I a ha
    start (fun _ _ h => ⟨h.1,h.2.1,(h.2.2.2.2 85 (by decide)).trans hp⟩) (by
      intro k hk s h
      let t := s.putData 0 ((2:K)^(k+1+2))
      have ht : t.AllData P := h.1.putData _ (powers (k+1) (by omega))
      have word : s.data 0+s.data 0=(2:K)^(k+1+2) := by
        rw [h.2.2.1,show k+1+2=k+2+1 by omega,pow_succ (2:K) (k+2)]; ring
      have add : Block.Eval (Memory.AllData P) (.op (.add 0 0 0)) s 1 t := by
        simpa only [word] using Block.Eval.op_add (safe := Memory.AllData P) s 0 0 0 h.1
          (h.1.putData _ (word ▸ powers (k+1) (by omega)))
      refine ⟨t,add,ht,by simp [t,h.2.1],by simp [t],?_,?_⟩
      · intro j ne; simpa [t,ne] using h.2.2.2.1 j ne
      · intro j ne; simpa [t,ne] using h.2.2.2.2 j ne)
  let t := u.putData (m.index 86) ((2:K)^(prec+2))
  have u86 := done.2.2.2.2 86 (by decide)
  have put : Block.Eval (Memory.AllData P) (.op (.store 86 0)) u 1 t := by
    simpa only [u86,done.2.2.1] using Block.Eval.op_store (safe := Memory.AllData P) u 86 0 done.1
      (done.1.putData _ (done.1 _))
  refine ⟨t,?_,by simp [t],?_,done.2.2.2.2⟩
  · rw [show prec*4+4=1+(prec*(1+3)+2+1) by omega]
    exact init.seq (dbl.seq put)
  · intro j h0 ne; simpa [t,ne] using done.2.2.2.1 j h0

end MinorProxyCache
end Compression
end LinearProgramming
end Optimization
end OAI

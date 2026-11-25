import OAI.Optimization.LinearProgramming.RAM.Array

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM

private def countPairBody (out : ℕ) : Block := .seq (.op (.incr 3 3)) <| .seq (.op (.incr 3 3)) <|
  .seq (.op (.incr 1 1)) <| .seq (.op (.incr 1 1)) <| .seq (.op (.incr out out)) (.op (.add 5 5 6))

/-- Decode an even-scaled address, adding its half to a scalar count and its full value
to the pointer in address 1. Only odd address registers are modified. -/
def unpackCount (src out : ℕ) : Block := .seq (.op (.addrConst out 0)) <|
  .seq (.op (.addrConst 3 0)) (.loop (.addrLT 3 src) (countPairBody out))

theorem unpackCount_spec (m : Memory ℚ) (src out n base acc : ℕ) {P : ℚ → Prop}
    (safe : m.AllData P) (hs : src=0 ∨ src=2) (ho : out=7 ∨ out=9)
    (input : m.index src=2*n) (ptr : m.index 1=base) (init : m.data 5=(acc:ℚ))
    (one : m.data 6=1) (small : ∀ z : ℕ, z≤acc+n → P (z:ℚ)) :
    ∃ t, Block.Eval (Memory.AllData P) (unpackCount src out) m (8*n+3) t ∧
      t.index out=n ∧ t.index 1=base+2*n ∧ t.data 5=((acc+n:ℕ):ℚ) ∧
      (∀ i, i≠1 → i≠3 → i≠out → t.index i=m.index i) ∧
      ∀ i, i≠5 → t.data i=m.data i := by
  have o1 : 1≠out := by omega
  have o3 : 3≠out := by omega
  let I := fun (j : ℕ) (s : Memory ℚ) => s.AllData P ∧ s.index 3=2*j ∧ s.index out=j ∧
    s.index 1=base+2*j ∧ s.data 5=((acc+j:ℕ):ℚ) ∧
    (∀ i, i≠1 → i≠3 → i≠out → s.index i=m.index i) ∧ (∀ i, i≠5 → s.data i=m.data i)
  let a := m.putIndex out 0
  let b := a.putIndex 3 0
  have ea := Block.Eval.op_addrConst m out 0 safe (safe.putIndex _ _)
  have eb := Block.Eval.op_addrConst a 3 0 ea.safe_end (ea.safe_end.putIndex _ _)
  have basecase : I 0 b := by
    refine ⟨eb.safe_end,by simp [b],by simp [b,a,Ne.symm o3],by simp [b,a,o1,ptr],by simpa [b,a] using init,?_,fun _ _ => rfl⟩
    intro i _ i3 io; simp [b,a,i3,io]
  have advance (j : ℕ) (hj : j<n) (s : Memory ℚ) (h : I j s) :
      (Cond.addrLT 3 src).test s=true ∧ ∃ t, Block.Eval (Memory.AllData P) (countPairBody out) s 6 t ∧ I (j+1) t := by
    obtain ⟨s0,cnt,width,pos,val,fi,fd⟩ := h
    have ineq := (fi src (by omega) (by omega) (by omega)).trans input
    refine ⟨by simp [Cond.test,cnt,ineq,hj],?_⟩
    let a1 := s.putIndex 3 (s.index 3+1)
    let a2 := a1.putIndex 3 (a1.index 3+1)
    let a3 := a2.putIndex 1 (a2.index 1+1)
    let a4 := a3.putIndex 1 (a3.index 1+1)
    let a5 := a4.putIndex out (a4.index out+1)
    let t := a5.putData 5 (a5.data 5+a5.data 6)
    have hupdate : a5.data 5+a5.data 6=((acc+(j+1):ℕ):ℚ) := by
      change s.data 5+s.data 6=_
      rw [val,(fd 6 (by decide)).trans one]; push_cast; ring
    have e1 := Block.Eval.op_incr s 3 3 s0 (s0.putIndex _ _)
    have e2 := Block.Eval.op_incr a1 3 3 e1.safe_end (e1.safe_end.putIndex _ _)
    have e3 := Block.Eval.op_incr a2 1 1 e2.safe_end (e2.safe_end.putIndex _ _)
    have e4 := Block.Eval.op_incr a3 1 1 e3.safe_end (e3.safe_end.putIndex _ _)
    have e5 := Block.Eval.op_incr a4 out out e4.safe_end (e4.safe_end.putIndex _ _)
    have e6 := Block.Eval.op_add a5 5 5 6 e5.safe_end (e5.safe_end.putData _ (hupdate ▸ small _ (by omega)))
    refine ⟨t,e1.seq (e2.seq (e3.seq (e4.seq (e5.seq e6)))),e6.safe_end,?_,?_,?_,?_,?_,?_⟩
    · simp [t,a5,a4,a3,a2,a1,o3,cnt]; omega
    · simp [t,a5,a4,a3,a2,a1,Ne.symm o1,Ne.symm o3,width]
    · simp [t,a5,a4,a3,a2,a1,o1,pos]; omega
    · simpa [t] using hupdate
    · intro i i1 i3 io; simpa [t,a5,a4,a3,a2,a1,i1,i3,io] using fi i i1 i3 io
    · intro i h; simpa [t,h,a5,a4,a3,a2,a1] using fd i h
  have stop (s : Memory ℚ) (h : I n s) : (Cond.addrLT 3 src).test s=false ∧ s.AllData P := by
    obtain ⟨ss,cnt,_,_,_,fi,_⟩ := h
    exact ⟨by simp [Cond.test,cnt,(fi src (by omega) (by omega) (by omega)).trans input],ss⟩
  obtain ⟨t,run,_,_,result,pos,val,fi,fd⟩ := Block.Eval.loop_invariant_exact I b n 6 basecase advance stop
  refine ⟨t,?_,result,pos,val,fi,fd⟩
  simpa only [unpackCount,show 1+(1+(n*(6+2)+1))=8*n+3 by omega] using ea.seq (eb.seq run)

end Compression
end LinearProgramming
end Optimization
end OAI

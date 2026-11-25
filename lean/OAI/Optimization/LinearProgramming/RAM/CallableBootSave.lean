import OAI.Optimization.LinearProgramming.RAM.Array

/-! Save the original low address words before borrowing those registers. The dynamic
backup starts immediately past the declared address cap. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Callable
namespace Boot

open Block

def saveFrom (src : ℕ) : ℕ → Block
  | 0 => .skip
  | n+1 => .seq (.op (.incr 0 0)) <| .seq (.op (.addrStore 0 src)) (saveFrom (src+1) n)

def retreat (r : ℕ) : ℕ → Block
  | 0 => .skip
  | n+1 => .seq (.op (.decr r r)) (retreat r n)

def saveBlock : Block := .seq (saveFrom 3 9) (retreat 0 9)

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem retreat_spec (P : K → Prop) (r n : ℕ) (s : Memory K) (hs : s.AllData P) :
    ∃ t, Eval (Memory.AllData P) (retreat r n) s n t ∧ t.data=s.data ∧
      t.index r=s.index r-n ∧ ∀ a, a≠r → t.index a=s.index a := by
  induction n generalizing s with
  | zero => exact ⟨s,.skip hs,rfl,rfl,fun _ _ => rfl⟩
  | succ n ih =>
    let u := s.putIndex r (s.index r-1)
    have step := Eval.op_decr (safe:=Memory.AllData P) s r r hs hs
    obtain ⟨t,run,hd,hp,hf⟩ := ih u hs
    refine ⟨t,?_,hd,?_,?_⟩
    · simpa [retreat,Nat.one_add] using step.seq run
    · simpa [u,Nat.sub_sub,Nat.one_add] using hp
    · intro a ha
      simpa [u,ha] using hf a ha

theorem saveFrom_spec (P : K → Prop) (src n p : ℕ) (s : Memory K) (hs : s.AllData P)
    (hp : s.index 0=p) (hsrc : 0 < src) (hsep : src+n ≤ p) :
    ∃ t, Eval (Memory.AllData P) (saveFrom src n) s (2*n) t ∧ t.data=s.data ∧
      t.index 0=p+n ∧ (∀ j < n, t.index (p+1+j)=s.index (src+j)) ∧
      ∀ r, r≠0 → (r ≤ p ∨ p+n < r) → t.index r=s.index r := by
  induction n generalizing p src s with
  | zero => exact ⟨s,.skip hs,rfl,hp,fun j h => (Nat.not_lt_zero _ h).elim,fun _ _ _ => rfl⟩
  | succ n ih =>
    let a := s.putIndex 0 (p+1)
    let u := a.putIndex (p+1) (s.index src)
    have e1 : Eval (Memory.AllData P) (.op (.incr 0 0)) s 1 a := by
      simpa only [a,hp] using Eval.op_incr s 0 0 hs hs
    have e2 : Eval (Memory.AllData P) (.op (.addrStore 0 src)) a 1 u := by
      simpa [a,u,show src≠0 by omega] using Eval.op_addrStore a 0 src hs hs
    have p' : u.index 0=p+1 := by simp [u,a]
    obtain ⟨t,run,dat,ptr,wr,fr⟩ := ih (src+1) (p+1) u hs p' (by omega) (by omega)
    refine ⟨t,?_,dat,by omega,?_,?_⟩
    · simpa only [saveFrom,show 2*(n+1)=1+(1+2*n) by omega] using e1.seq (e2.seq run)
    · rintro (_|j) hj
      · have first := fr (p+1) (by omega) (.inl le_rfl)
        simpa [u,a] using first
      · have h := wr j (by omega)
        have value : u.index (src+1+j)=s.index (src+1+j) :=
          (Memory.putIndex_ne a (by omega) _).trans (Memory.putIndex_ne s (by omega) _)
        rw [show p+1+(j+1)=p+1+1+j by omega,show src+(j+1)=src+1+j by omega]
        exact h.trans value
    · intro r hr he
      have neq : r≠p+1 := by omega
      simpa [u,a,hr,neq] using fr r hr (by omega)

theorem saveBlock_spec (P : K → Prop) (s : Memory K) (cap : ℕ) (hs : s.AllData P)
    (h0 : s.index 0=cap) (hc : 12 ≤ cap) :
    ∃ t, Eval (Memory.AllData P) saveBlock s 27 t ∧ t.data=s.data ∧
      t.index 0=cap ∧ (∀ j < 9, t.index (cap+1+j)=s.index (3+j)) ∧
      ∀ r, (r ≤ cap ∨ cap+9 < r) → t.index r=s.index r := by
  obtain ⟨m,e,da,cap',wr,fr⟩ := saveFrom_spec P 3 9 cap s hs h0 (by decide) hc
  obtain ⟨t,f,dt,p,ff⟩ := retreat_spec P 0 9 m e.safe_end
  have end0 : t.index 0=cap := by omega
  refine ⟨t,e.seq f,dt.trans da,end0,?_,?_⟩
  · intro j hj
    exact (ff _ (by omega)).trans (wr j hj)
  · intro r hr
    by_cases h : r=0
    · simpa [h,h0] using end0
    · exact (ff _ h).trans (fr r h hr)

end Boot
end Callable
end RAM
end LinearProgramming
end Optimization
end OAI

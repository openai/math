import OAI.Optimization.LinearProgramming.RAM.Loops
import Mathlib.Tactic

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Copy a scalar into a contiguous array. Scalar source and destination must be disjoint. -/
def fillBlock (value base ptr idx size : Nat) : Block :=
  .seq (.op (.addrCopy ptr base))
    (.forRange idx size (.seq (.op (.store ptr value)) (.op (.incr ptr ptr))))

/-- Complete frame and exact instruction count of the constant-array write. -/
theorem fillBlock_correct (P : K → Prop) (m : Memory K) (value base ptr idx size n : Nat)
    (hpi : ptr≠idx) (hps : ptr≠size) (his : idx≠size) (hn : m.index size=n)
    (hval : value<m.index base) (hm : ∀ k, P (m.data k)) :
    ∃ t, Block.Eval (fun s => ∀ k, P (s.data k)) (fillBlock value base ptr idx size) m (5*n+3) t ∧
      (∀ j<n, t.data (m.index base+j)=m.data value) ∧
      (∀ k, k<m.index base ∨ m.index base+n≤k → t.data k=m.data k) ∧
      t.index idx=n ∧ t.index ptr=m.index base+n ∧
      (∀ k, k≠idx → k≠ptr → t.index k=m.index k) := by
  let safe (s : Memory K) := ∀ k, P (s.data k)
  let I (j : Nat) (s : Memory K) := safe s ∧
    (∀ k<j, s.data (m.index base+k) = m.data value) ∧
    (∀ k, k<m.index base ∨ m.index base+j≤k → s.data k=m.data k) ∧
    s.index idx=j ∧ s.index ptr=m.index base+j ∧
    (∀ k, k≠idx → k≠ptr → s.index k=m.index k)
  let m1 := m.putIndex ptr (m.index base)
  have init : I 0 (m1.putIndex idx 0) := by
    refine ⟨hm,fun k hk => (Nat.not_lt_zero _ hk).elim,fun _ _ => rfl,?_,?_,?_⟩
    · simp
    · simp [m1,hpi]
    · intro k hi hp; simp [m1,hi,hp]
  obtain ⟨t,et,hsend,hcells,hframe,hidx,hptr,hif⟩ :=
    Block.Eval.forRange_invariant_exact (body := .seq (.op (.store ptr value)) (.op (.incr ptr ptr)))
      idx size n 2 I m1 hm init
      (fun _ s h => ⟨h.1,h.2.2.2.1,(h.2.2.2.2.2 _ his.symm hps.symm).trans hn⟩)
      (fun j _ s ⟨hs,hcells,hframe,hidx,hptr,hif⟩ => by
        let u := s.putData (s.index ptr) (s.data value)
        let v := u.putIndex ptr (u.index ptr+1)
        have hu : safe u := by
          intro k
          by_cases hk : k=s.index ptr
          · simpa [u,hk] using hs value
          · simpa [u,hk] using hs k
        refine ⟨v,(Block.Eval.op_store s ptr value hs hu).seq (Block.Eval.op_incr u ptr ptr hu hu),
          hu,?_,?_,?_,?_,?_⟩
        · intro k hk
          by_cases hk' : k=j
          · subst k
            simpa [v,u,hptr] using hframe _ (Or.inl hval)
          · have hne : m.index base+k ≠ s.index ptr := by rw [hptr];omega
            simpa [v,u,hne] using hcells k (by omega)
        · intro k hk
          have hne : k≠s.index ptr := by rw [hptr];omega
          simpa [v,u,hne] using hframe k (by omega)
        · simp [v,u,hpi.symm,hidx]
        · simp [v,u,hpi,hptr,Nat.add_assoc]
        · intro k hi hp; simpa [v,u,hi,hp] using hif k hi hp)
  refine ⟨t,?_,hcells,hframe,hidx,hptr,hif⟩
  have e := (Block.Eval.op_addrCopy m ptr base hm hm).seq et
  rw [show 5*n+3 = 1+(n*(2+3)+2) by ring]
  exact e

/-- Advance a pointer by a dynamic address-bank count without assuming address addition. -/
def seekBlock (base ptr idx size : Nat) : Block :=
  .seq (.op (.addrCopy ptr base)) (.forRange idx size (.op (.incr ptr ptr)))

theorem seekBlock_correct (P : K → Prop) (m : Memory K) (base ptr idx size n : Nat)
    (hpi : ptr≠idx) (hps : ptr≠size) (his : idx≠size) (hn : m.index size=n)
    (hm : ∀ k, P (m.data k)) :
    ∃ t, Block.Eval (fun s => ∀ k, P (s.data k)) (seekBlock base ptr idx size) m (4*n+3) t ∧
      t.data=m.data ∧ t.index idx=n ∧ t.index ptr=m.index base+n ∧
      (∀ k, k≠idx → k≠ptr → t.index k=m.index k) := by
  let m1 := m.putIndex ptr (m.index base)
  let I (j : Nat) (s : Memory K) := s.data=m.data ∧
    s.index idx=j ∧ s.index ptr=m.index base+j ∧ (∀ k, k≠idx → k≠ptr → s.index k=m.index k)
  have init : I 0 (m1.putIndex idx 0) := by
    refine ⟨rfl,by simp,by simp [m1,hpi],?_⟩
    intro k hi hp; simp [m1,hi,hp]
  obtain ⟨t,et,hd,hidx,hptr,hif⟩ :=
    Block.Eval.forRange_invariant_exact (safe := fun s => ∀ k, P (s.data k)) (body := .op (.incr ptr ptr))
      idx size n 1 I m1 hm init
      (fun _ s h => ⟨h.1.symm ▸ hm,h.2.1,(h.2.2.2 _ his.symm hps.symm).trans hn⟩)
      (fun j _ s ⟨hd,hi,hp,hf⟩ => by
        let u := s.putIndex ptr (s.index ptr+1)
        have hs : ∀ k, P (s.data k) := hd.symm ▸ hm
        refine ⟨u,Block.Eval.op_incr s ptr ptr hs hs,hd,by simp [u,hpi.symm,hi],
          by simp [u,hpi,hp,Nat.add_assoc],?_⟩
        intro k hk hk'; simpa [u,hk,hk'] using hf k hk hk')
  refine ⟨t,?_,hd,hidx,hptr,hif⟩
  have e := (Block.Eval.op_addrCopy m ptr base hm hm).seq et
  rw [show 4*n+3 = 1+(n*(1+3)+2) by ring]
  exact e

end RAM
end LinearProgramming
end Optimization
end OAI

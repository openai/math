import OAI.Optimization.LinearProgramming.RAM.Loops
import Mathlib.Tactic.Ring

/-! Conversion of an address-bank count to a scalar without inspecting scalar bits. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Initialize scalar registers `dst` and `one`, then count up to the address in `size`. -/
def natCastBlock (dst one idx size : ℕ) : Block :=
  .seq (.op (.const dst 0)) (.seq (.op (.const one 1))
    (.forRange idx size (.op (.add dst dst one))))

/-- The exact linear conversion run updates only the two scalar registers and the address counter.
Its scalar intermediate values are the successive natural numbers, from zero through the bound. -/
theorem natCastBlock_correct (P : K → Prop) (m : Memory K)
    (dst one idx size n : ℕ) (hd : dst≠one) (hi : idx≠size) (hn : m.index size=n)
    (hm : ∀ k, P (m.data k)) (h1 : P 1) (hval : ∀ j≤n, P (j : K)) :
    ∃ t, Block.Eval (fun m => ∀ k, P (m.data k)) (natCastBlock dst one idx size)
      m (4*n+4) t ∧ t.data dst=(n : K) ∧ t.data one=1 ∧ t.index idx=n ∧
      (∀ k, k≠idx → t.index k=m.index k) ∧
      (∀ k, k≠dst → k≠one → t.data k=m.data k) := by
  let safe (s : Memory K) := ∀ k, P (s.data k)
  have upd {s : Memory K} {k : ℕ} {x : K} (hs : safe s) (hx : P x) : safe (s.putData k x) := by
    intro a
    by_cases h : a=k
    · simpa [Memory.putData,h] using hx
    · simpa [Memory.putData,Function.update_of_ne h] using hs a
  let m1 := m.putData dst 0
  let m2 := m1.putData one 1
  have hm1 : safe m1 := upd hm (by simpa using hval 0 (Nat.zero_le _))
  have hm2 : safe m2 := upd hm1 h1
  let I (j : ℕ) (s : Memory K) := safe s ∧ s.data dst = (j:K) ∧ s.data one=1 ∧ s.index idx=j ∧
    (∀ k, k≠idx → s.index k=m.index k) ∧ (∀ k, k≠dst → k≠one → s.data k=m.data k)
  have init : I 0 (m2.putIndex idx 0) := by
    refine ⟨hm2,?_,?_,?_,?_,?_⟩
    · simp [m2,m1,Memory.putIndex,Memory.putData,Function.update_of_ne hd]
    · simp [m2,Memory.putIndex,Memory.putData]
    · simp [Memory.putIndex]
    · intro k h
      simp [m2,m1,Memory.putIndex,Memory.putData,Function.update_of_ne h]
    · intro k h k'
      simp [m2,m1,Memory.putIndex,Memory.putData,Function.update_of_ne h,Function.update_of_ne k']
  obtain ⟨t, et, hsafe, hdst, hone, hidx, hif, hdf⟩ :=
    Block.Eval.forRange_invariant_exact (body := .op (.add dst dst one))
      idx size n 1 I m2 hm2 init (fun j s h => ⟨h.1,h.2.2.2.1,(h.2.2.2.2.1 _ hi.symm).trans hn⟩)
      (fun j hj s ⟨hs,hdst,hone,hidx,hif,hdf⟩ => by
        let u := s.putData dst (s.data dst+s.data one)
        have hsum : s.data dst+s.data one = ((j+1:ℕ):K) := by simp [hdst,hone]
        have hu : safe u := upd hs (hsum ▸ hval (j+1) hj)
        refine ⟨u,Block.Eval.op_add s dst dst one hs hu,hu,?_,?_,?_,?_,?_⟩
        · simpa [u,Memory.putIndex,Memory.putData] using hsum
        · simpa [u,Memory.putIndex,Memory.putData,Function.update_of_ne hd.symm] using hone
        · simp [u,Memory.putIndex,Memory.putData,hidx]
        · intro k h
          simpa [u,Memory.putIndex,Memory.putData,Function.update_of_ne h] using hif _ h
        · intro k h k'
          simpa [u,Memory.putIndex,Memory.putData,Function.update_of_ne h] using hdf _ h k')
  have e₀ : Block.Eval safe (.op (.const dst 0)) m 1 m1 := by
    simpa using Block.Eval.op_const m dst 0 hm (by simpa using hm1)
  have e₁ : Block.Eval safe (.op (.const one 1)) m1 1 m2 := by
    simpa using Block.Eval.op_const m1 one 1 hm1 (by simpa using hm2)
  have ei := e₀.seq (e₁.seq et)
  refine ⟨t,?_,hdst,hone,hidx,hif,hdf⟩
  rw [show 4*n+4 = 1+(1+(n*(1+3)+2)) by ring]
  exact ei

end RAM
end LinearProgramming
end Optimization
end OAI

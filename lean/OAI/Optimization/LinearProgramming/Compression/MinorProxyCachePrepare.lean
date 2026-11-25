import OAI.Optimization.LinearProgramming.Compression.MinorProxyInputsStep

/-! Clear the native proxy's scratch cells and restore the next positive argument.
No previous numerator or partially evaluated logarithm can enlarge a later call's bit budget. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace MinorProxyCache
open RAM

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def clearNative : Block := .seq (.op (.const 0 0)) (.forRange 63 79 (.op (.store 63 0)))

theorem clearNative_eval (P : K → Prop) (m : Memory K) (hm : m.AllData P) (hz : P 0) :
    ∃ t, Block.Eval (Memory.AllData P) clearNative m (m.index 79*4+3) t ∧
      (∀ j, t.data j = if j<m.index 79 ∨ j=0 then 0 else m.data j) ∧
      ∀ j, j≠63 → t.index j=m.index j := by
  let a := m.putData 0 0
  have ha : a.AllData P := hm.putData 0 hz
  have const : Block.Eval (Memory.AllData P) (.op (.const 0 0)) m 1 a := by
    simpa [a] using Block.Eval.op_const m 0 0 hm (by simpa [a] using ha)
  let I (k : ℕ) (s : Memory K) := s.AllData P ∧ s.index 63=k ∧
    (∀ j, s.data j=if j<k ∨ j=0 then 0 else m.data j) ∧ ∀ j,j≠63 → s.index j=m.index j
  have init : I 0 (a.putIndex 63 0) := by
    refine ⟨ha,by simp,?_,?_⟩
    · intro j; by_cases h : j=0 <;> simp [a,h]
    · intro j h; simp [a,h]
  obtain ⟨t,run,fin⟩ := Block.Eval.forRange_invariant_exact (safe := Memory.AllData P) 63 79
    (m.index 79) 1 I a ha init (fun _ _ h => ⟨h.1,h.2.1,h.2.2.2 79 (by decide)⟩) (by
      intro k _ s h
      let u := s.putData k 0
      have keep : u.AllData P := h.1.putData _ hz
      have s0 : s.data 0=0 := by simpa using h.2.2.1 0
      have step : Block.Eval (Memory.AllData P) (.op (.store 63 0)) s 1 u := by
        have e := Block.Eval.op_store (safe := Memory.AllData P) s 63 0 h.1 (h.1.putData _ (h.1 0))
        simpa only [h.2.1,s0,u] using e
      refine ⟨u,step,keep,by simp [u,h.2.1],?_,?_⟩
      · intro j
        by_cases eq : j=k
        · subst j; simp [u]
        · have lt : j<k+1 ↔ j<k := by omega
          simp [u,eq,lt,h.2.2.1 j]
      · intro j hj; simpa [u,hj] using h.2.2.2 j hj)
  refine ⟨t,?_,fin.2.2.1,fin.2.2.2⟩
  rw [show m.index 79*4+3 = 1+(m.index 79*(1+3)+2) by omega]
  exact const.seq run

def prepare : Block := .seq clearNative (.seq (.op (.load 0 57))
  (.seq (.op (.addrCopy 0 84)) (.op (.addrCopy 1 85))))

theorem prepare_eval (P : K → Prop) (s : Memory K) (hs : s.AllData P) (hz : P 0)
    (pos : 0<s.index 79) (guarded : s.index 79≤s.index 57) :
    ∃ t, Block.Eval (Memory.AllData P) prepare s (s.index 79*4+6) t ∧
      t.data 0=s.data (s.index 57) ∧ t.index 0=s.index 84 ∧ t.index 1=s.index 85 ∧
      (∀ j, 0<j → j<s.index 79 → t.data j=0) ∧
      (∀ j, s.index 79≤j → t.data j=s.data j) ∧
      ∀ j, 11≤j → j≠63 → t.index j=s.index j := by
  obtain ⟨u,clear,vals,ids⟩ := clearNative_eval P s hs hz
  have src : u.data (u.index 57)=s.data (s.index 57) := by
    rw [ids 57 (by decide),vals,ite_eq_right (by omega)]
  let a := u.putData 0 (s.data (s.index 57))
  let b := a.putIndex 0 (s.index 84)
  let t := b.putIndex 1 (s.index 85)
  have e1 : Block.Eval (Memory.AllData P) (.op (.load 0 57)) u 1 a := by
    simpa only [src] using Block.Eval.op_load (safe := Memory.AllData P) u 0 57 clear.safe_end
      (clear.safe_end.putData _ (clear.safe_end _))
  have a84 : a.index 84=s.index 84 := ids 84 (by decide)
  have b85 : b.index 85=s.index 85 := by simpa [b,a] using ids 85 (by decide)
  have e2 : Block.Eval (Memory.AllData P) (.op (.addrCopy 0 84)) a 1 b := by
    simpa only [a84] using Block.Eval.op_addrCopy (safe := Memory.AllData P) a 0 84 e1.safe_end e1.safe_end
  have e3 : Block.Eval (Memory.AllData P) (.op (.addrCopy 1 85)) b 1 t := by
    simpa only [b85] using Block.Eval.op_addrCopy (safe := Memory.AllData P) b 1 85 e2.safe_end e2.safe_end
  refine ⟨t,?_,by simp [t,b,a],by simp [t,b],by simp [t],?_,?_,?_⟩
  · rw [show s.index 79*4+6=s.index 79*4+3+(1+(1+1)) by omega]
    exact clear.seq (e1.seq (e2.seq e3))
  · intro j hj h; simp [t,b,a,show j≠0 by omega,vals j,h]
  · intro j hj; simp [t,b,a,show j≠0 by omega,vals j,show ¬j<s.index 79 by omega]
  · intro j hj h63; simpa [t,b,a,show j≠0 by omega,show j≠1 by omega] using ids j h63

end MinorProxyCache
end Compression
end LinearProgramming
end Optimization
end OAI
